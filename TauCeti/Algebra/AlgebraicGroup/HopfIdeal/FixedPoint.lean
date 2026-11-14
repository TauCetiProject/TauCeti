/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Action
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Equalizer
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.FixedPoint
public import TauCeti.RingTheory.Smooth.FixedPointIdeal

/-!
# Fixed-point Hopf ideals of affine group-scheme endomorphisms and Edixhoven's theorem

For `H : CommHopfAlgCat R` and endomorphisms `f : ι → (H ⟶ H)`, building on
`TauCeti.HopfIdeal.fixedPoint`, this file defines the bundled fixed-point Hopf ideals
`TauCeti.CommHopfAlgCat.fixedPointHopfIdeal` and
`TauCeti.FiniteTypeCommHopfAlgCat.fixedPointHopfIdeal`. On `A`-points, the subgroup cut out by
`fixedPointHopfIdeal f` consists of points fixed by every `BialgHom.mapDomain (f i).hom`
(`mem_quotientPointsSubgroup_fixedPointHopfIdeal_iff`,
`range_mapDomain_mkQuotient_fixedPointHopfIdeal`).

For a monoid action `ρ : Θ →* CategoryTheory.End H`, the underlying ideal of
`fixedPointHopfIdeal (fun θ ↦ (ρ θ).asHom)` coincides with `MulSemiringAction.fixedPointIdeal Θ H`
(`CommHopfAlgCat.fixedPointHopfIdeal_toIdeal_eq_fixedPointIdeal`); a group action
`ρ : Θ →* CategoryTheory.Aut H` factors through `CategoryTheory.Aut.toEnd`. Combining with
`MulSemiringAction.smooth_quotient_fixedPointIdeal` yields **Edixhoven's tame fixed-point theorem**
(`CommHopfAlgCat.smooth_quotient_fixedPointHopfIdeal`,
`FiniteTypeCommHopfAlgCat.smooth_quotient_fixedPointHopfIdeal`,
`FiniteTypeCommHopfAlgCat.exists_smooth_fixedPoints`). The sharpness example `(𝔾ₘ)^{-1} ≃ μ₂` lives
in `TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Inversion`.

## Main declarations

* `TauCeti.CommHopfAlgCat.fixedPointHopfIdeal`, `TauCeti.CommHopfAlgCat.liftFixedPoint`, and
  `TauCeti.FiniteTypeCommHopfAlgCat.fixedPointHopfIdeal`: bundled fixed-point Hopf ideals.
* `CommHopfAlgCat.fixedPointHopfIdeal_toIdeal_eq_fixedPointIdeal`,
  `CommHopfAlgCat.smooth_quotient_fixedPointHopfIdeal`, and
  `TauCeti.FiniteTypeCommHopfAlgCat.exists_smooth_fixedPoints`: Edixhoven's smoothness theorem.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), Propositions 3.1
  and 3.4, pp. 293–295.
* J. S. Milne, *Algebraic Groups*, Cambridge University Press (2017), §1.h and §12.
-/

public section

open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom
open CategoryTheory WithConv

universe u v w u'

namespace TauCeti.CommHopfAlgCat

section Morphisms

variable {R : Type u} [CommRing R] {H T : _root_.CommHopfAlgCat.{v} R} {ι : Sort w}

private theorem hom_id_eq_bialgHom_id : (𝟙 H : H ⟶ H).hom = BialgHom.id R H := by ext; simp

/-- The **fixed-point Hopf ideal** of endomorphisms `f : ι → (H ⟶ H)` in `CommHopfAlgCat R`. -/
noncomputable def fixedPointHopfIdeal (f : ι → (H ⟶ H)) : HopfIdeal R H :=
  HopfIdeal.fixedPoint fun i ↦ (f i).hom

/-- `fixedPointHopfIdeal f` is `HopfIdeal.fixedPoint` on the underlying bialgebra morphisms. -/
theorem fixedPointHopfIdeal_def (f : ι → (H ⟶ H)) :
    fixedPointHopfIdeal f = HopfIdeal.fixedPoint fun i ↦ (f i).hom := (rfl)

/-- `fixedPointHopfIdeal f` is the supremum of `equalizerHopfIdeal (f i) (𝟙 H)`. -/
theorem fixedPointHopfIdeal_eq_iSup_equalizerHopfIdeal (f : ι → (H ⟶ H)) :
    fixedPointHopfIdeal f = ⨆ i, equalizerHopfIdeal (f i) (𝟙 H) := by
  simp_rw [fixedPointHopfIdeal_def, HopfIdeal.fixedPoint_def, equalizerHopfIdeal_def,
    hom_id_eq_bialgHom_id]

/-- A morphism `p : H ⟶ T` kills `fixedPointHopfIdeal f` iff `f i ≫ p = p` for all `i`. -/
theorem fixedPointHopfIdeal_toIdeal_le_ker_iff (f : ι → (H ⟶ H)) (p : H ⟶ T) :
    (fixedPointHopfIdeal f).toIdeal ≤ RingHom.ker p.hom.toAlgHom.toRingHom ↔
      ∀ i, f i ≫ p = p := by
  rw [fixedPointHopfIdeal_eq_iSup_equalizerHopfIdeal, HopfIdeal.iSup_toIdeal, iSup_le_iff]
  exact forall_congr' fun i ↦
    (equalizerHopfIdeal_toIdeal_le_ker_iff (f i) (𝟙 H) p).trans (by rw [Category.id_comp])

/-- `fixedPointHopfIdeal f` vanishes if and only if every `f i` is `𝟙 H`. -/
@[simp]
theorem fixedPointHopfIdeal_eq_bot_iff (f : ι → (H ⟶ H)) :
    fixedPointHopfIdeal f = ⊥ ↔ ∀ i, f i = 𝟙 H := by
  rw [fixedPointHopfIdeal_def, HopfIdeal.fixedPoint_eq_bot_iff, ← hom_id_eq_bialgHom_id]
  exact forall_congr' fun _ ↦ ⟨_root_.CommHopfAlgCat.hom_ext, congrArg Hom.hom⟩

/-- The quotient morphism by `fixedPointHopfIdeal f` coequalizes every `f i` with `𝟙 H`. -/
theorem comp_mkQuotient_fixedPointHopfIdeal (f : ι → (H ⟶ H)) (i : ι) :
    f i ≫ mkQuotient H (fixedPointHopfIdeal f) = mkQuotient H (fixedPointHopfIdeal f) :=
  ((fixedPointHopfIdeal_toIdeal_le_ker_iff f (mkQuotient H (fixedPointHopfIdeal f))).mp
    (mkQuotient_ker H (fixedPointHopfIdeal f)).ge) i

/-- **Coequalizer universal property.** Any `p : H ⟶ T` with `∀ i, f i ≫ p = p` factors through
`quotient H (fixedPointHopfIdeal f)`. -/
noncomputable def liftFixedPoint {f : ι → (H ⟶ H)} (p : H ⟶ T) (hp : ∀ i, f i ≫ p = p) :
    quotient H (fixedPointHopfIdeal f) ⟶ T :=
  liftQuotient (fixedPointHopfIdeal f) p ((fixedPointHopfIdeal_toIdeal_le_ker_iff f p).mpr hp)

/-- `liftFixedPoint p hp` precomposed with `mkQuotient` recovers `p`. -/
@[simp]
theorem mkQuotient_comp_liftFixedPoint {f : ι → (H ⟶ H)} (p : H ⟶ T) (hp : ∀ i, f i ≫ p = p) :
    mkQuotient H (fixedPointHopfIdeal f) ≫ liftFixedPoint p hp = p :=
  mkQuotient_comp_liftQuotient _ _ _

/-- Any morphism out of `quotient H (fixedPointHopfIdeal f)` factoring `p` equals
`liftFixedPoint p hp`. -/
theorem liftFixedPoint_unique {f : ι → (H ⟶ H)} (p : H ⟶ T) (hp : ∀ i, f i ≫ p = p)
    (q : quotient H (fixedPointHopfIdeal f) ⟶ T)
    (hq : mkQuotient H (fixedPointHopfIdeal f) ≫ q = p) : q = liftFixedPoint p hp :=
  liftQuotient_unique _ _ _ q hq

/-- **Points of the fixed-point subgroup.** An `A`-point of `H` lies in the subgroup cut out by
`fixedPointHopfIdeal f` iff it is fixed by every `BialgHom.mapDomain (f i).hom`. -/
theorem mem_quotientPointsSubgroup_fixedPointHopfIdeal_iff (f : ι → (H ⟶ H))
    (A : CommAlgCat.{u'} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    x ∈ quotientPointsSubgroup H (fixedPointHopfIdeal f) A ↔
      ∀ i, BialgHom.mapDomain (f i).hom x = x := by
  rw [fixedPointHopfIdeal_eq_iSup_equalizerHopfIdeal,
    _root_.CommHopfAlgCat.quotientPointsSubgroup_iSup, Subgroup.mem_iInf]
  refine forall_congr' fun i ↦ ?_
  rw [mem_quotientPointsSubgroup_equalizerHopfIdeal_iff, hom_id_eq_bialgHom_id,
    BialgHom.mapDomain_id, MonoidHom.id_apply]

/-- The image of `(mkQuotient H (fixedPointHopfIdeal f)).hom` on `A`-valued points is the set of
points fixed under every `f i`. -/
theorem range_mapDomain_mkQuotient_fixedPointHopfIdeal (f : ι → (H ⟶ H))
    {A : Type u'} [CommRing A] [Algebra R A] :
    Set.range (BialgHom.mapDomain (A := A) (mkQuotient H (fixedPointHopfIdeal f)).hom) =
      {g | ∀ i, BialgHom.mapDomain (A := A) (f i).hom g = g} := by
  rw [_root_.CommHopfAlgCat.range_mapDomain_mkQuotient]
  ext g
  rw [SetLike.mem_coe, mem_quotientPointsSubgroup_fixedPointHopfIdeal_iff, Set.mem_ofPred_eq]

end Morphisms

end TauCeti.CommHopfAlgCat

namespace CommHopfAlgCat

open TauCeti

variable {R : Type u} [CommRing R] (H : CommHopfAlgCat.{v} R)

/-- For `ρ : Θ →* CategoryTheory.End H`, the underlying ideal of
`fixedPointHopfIdeal (fun θ ↦ (ρ θ).asHom)` is `MulSemiringAction.fixedPointIdeal Θ H`. -/
theorem fixedPointHopfIdeal_toIdeal_eq_fixedPointIdeal {Θ : Type w} [Monoid Θ]
    (ρ : Θ →* CategoryTheory.End H) :
    letI := H.mulSemiringActionOfEnd ρ
    (TauCeti.CommHopfAlgCat.fixedPointHopfIdeal fun θ : Θ ↦ (ρ θ).asHom).toIdeal =
      MulSemiringAction.fixedPointIdeal Θ H := by
  let _ := H.mulSemiringActionOfEnd ρ
  rw [TauCeti.CommHopfAlgCat.fixedPointHopfIdeal_def, HopfIdeal.fixedPoint_toIdeal,
    MulSemiringAction.fixedPointIdeal_eq_iSup]
  refine iSup_congr fun θ ↦ (HopfIdeal.equalizerIdeal_eq_span _ _).trans ?_
  simp only [H.smul_mulSemiringActionOfEnd ρ, BialgHom.id_apply]

/-- **Edixhoven's tame fixed-point theorem for commutative Hopf algebras.** If a group `Θ` acts by
Hopf-algebra automorphisms on a smooth `H : CommHopfAlgCat R` and `(Nat.card Θ : R)` is invertible
in `R`, then `H.quotient (fixedPointHopfIdeal ...)` is smooth over `R`. -/
theorem smooth_quotient_fixedPointHopfIdeal {Θ : Type w} [Group Θ]
    (hH : smoothCommHopfAlgProperty R H) (ρ : Θ →* CategoryTheory.Aut H)
    (hΘ : IsUnit (Nat.card Θ : R)) :
    smoothCommHopfAlgProperty R
      (H.quotient
        (TauCeti.CommHopfAlgCat.fixedPointHopfIdeal fun θ : Θ ↦ (ρ θ).asIso.hom)) := by
  rw [smoothCommHopfAlgProperty_iff] at hH ⊢
  let ρEnd : Θ →* CategoryTheory.End H := CategoryTheory.Aut.toEnd.comp ρ
  let _ : MulSemiringAction Θ H := H.mulSemiringActionOfEnd ρEnd
  have _ : SMulCommClass Θ R H := H.smulCommClass_mulSemiringActionOfEnd ρEnd
  have hEq : (TauCeti.CommHopfAlgCat.fixedPointHopfIdeal fun θ : Θ ↦ (ρ θ).asIso.hom).toIdeal =
      MulSemiringAction.fixedPointIdeal Θ H := by
    simpa [ρEnd] using H.fixedPointHopfIdeal_toIdeal_eq_fixedPointIdeal ρEnd
  have _ : Algebra.Smooth R (H ⧸ MulSemiringAction.fixedPointIdeal Θ H) :=
    MulSemiringAction.smooth_quotient_fixedPointIdeal hΘ
  exact Algebra.Smooth.of_equiv (Ideal.quotientEquivAlgOfEq R hEq.symm)

end CommHopfAlgCat

namespace TauCeti.FiniteTypeCommHopfAlgCat

variable {k : Type u} [CommRing k]

/-- The **fixed-point Hopf ideal** of endomorphisms `f : ι → (H ⟶ H)` in
`FiniteTypeCommHopfAlgCat k`. -/
noncomputable def fixedPointHopfIdeal {H : FiniteTypeCommHopfAlgCat.{u, v} k} {ι : Sort w}
    (f : ι → (H ⟶ H)) : HopfIdeal k H :=
  CommHopfAlgCat.fixedPointHopfIdeal fun i ↦ (f i).hom

/-- Unfolding `FiniteTypeCommHopfAlgCat.fixedPointHopfIdeal` via
`CommHopfAlgCat.fixedPointHopfIdeal`. -/
theorem fixedPointHopfIdeal_def {H : FiniteTypeCommHopfAlgCat.{u, v} k} {ι : Sort w}
    (f : ι → (H ⟶ H)) :
    fixedPointHopfIdeal f = CommHopfAlgCat.fixedPointHopfIdeal fun i ↦ (f i).hom := (rfl)

/-- On `R`-valued points, the image of `mkQuotient H (fixedPointHopfIdeal f)` is the set of points
fixed under every `f i`. -/
theorem range_mapDomain_mkQuotient_fixedPointHopfIdeal {H : FiniteTypeCommHopfAlgCat.{u, v} k}
    {ι : Sort w} (f : ι → (H ⟶ H)) {R : Type u'} [CommRing R] [Algebra k R] :
    Set.range (BialgHom.mapDomain (A := R) (toBialgHom (mkQuotient H (fixedPointHopfIdeal f)))) =
      {g | ∀ i, BialgHom.mapDomain (A := R) (toBialgHom (f i)) g = g} :=
  CommHopfAlgCat.range_mapDomain_mkQuotient_fixedPointHopfIdeal (fun i ↦ (f i).hom)

/-- **Edixhoven's theorem for `FiniteTypeCommHopfAlgCat` (explicit quotient form).** -/
theorem smooth_quotient_fixedPointHopfIdeal (H : FiniteTypeCommHopfAlgCat.{u, v} k)
    (hH : smoothCommHopfAlgProperty k H.obj) {Θ : Type w} [Group Θ]
    (ρ : Θ →* CategoryTheory.Aut H) (hΘ : IsUnit (Nat.card Θ : k)) :
    smoothCommHopfAlgProperty k
      (quotient H (fixedPointHopfIdeal fun θ : Θ ↦ (ρ θ).asIso.hom)).obj := by
  let ρObj : Θ →* CategoryTheory.Aut H.obj :=
    ((forget₂ (FiniteTypeCommHopfAlgCat.{u, v} k) (_root_.CommHopfAlgCat.{v} k)).mapAut H).comp ρ
  exact H.obj.smooth_quotient_fixedPointHopfIdeal hH ρObj hΘ

/-- **Edixhoven's tame fixed-point theorem for finite-type affine group schemes.** If `Θ` acts on a
smooth `H : FiniteTypeCommHopfAlgCat k` with `(Nat.card Θ : k)` invertible in `k`, there exist a
smooth `H'` and a surjective `f : H ⟶ H'` representing the `Θ`-fixed points on all `k`-algebras. -/
theorem exists_smooth_fixedPoints (H : FiniteTypeCommHopfAlgCat.{u, v} k)
    (hH : smoothCommHopfAlgProperty k H.obj) (Θ : Type w) [Group Θ]
    (ρ : Θ →* CategoryTheory.Aut H) (hΘ : IsUnit (Nat.card Θ : k)) :
    ∃ (H' : FiniteTypeCommHopfAlgCat.{u, v} k) (f : H ⟶ H'),
      smoothCommHopfAlgProperty k H'.obj ∧ Function.Surjective f.hom.hom ∧
      ∀ (R : Type u') [CommRing R] [Algebra k R],
        Set.range (BialgHom.mapDomain (A := R) (f.hom.hom : (H : Type v) →ₐc[k] H')) =
          {g | ∀ θ : Θ,
            BialgHom.mapDomain (A := R) ((ρ θ).asIso.hom.hom.hom : (H : Type v) →ₐc[k] H) g = g} :=
  ⟨quotient H (fixedPointHopfIdeal fun θ : Θ ↦ (ρ θ).asIso.hom),
    mkQuotient H (fixedPointHopfIdeal fun θ : Θ ↦ (ρ θ).asIso.hom),
    smooth_quotient_fixedPointHopfIdeal H hH ρ hΘ,
    CommHopfAlgCat.mkQuotient_surjective H.obj _,
    fun _ _ _ ↦ range_mapDomain_mkQuotient_fixedPointHopfIdeal (fun θ : Θ ↦ (ρ θ).asIso.hom)⟩

end TauCeti.FiniteTypeCommHopfAlgCat
