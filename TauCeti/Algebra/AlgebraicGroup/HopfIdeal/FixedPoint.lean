/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Equalizer
public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Inclusion
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import TauCeti.Algebra.MonoidAlgebra.MapDomain
public import TauCeti.Algebra.MonoidAlgebra.Smooth
public import TauCeti.RingTheory.Smooth.FixedPointIdeal
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Augmentation

/-!
# The fixed-point Hopf ideal of a family of group-scheme endomorphisms

Let `H` be a commutative Hopf `R`-algebra and `f : ι → (H →ₐc[R] H)` a family of bialgebra
endomorphisms. Contravariantly, `Spec H` is an affine group scheme over `Spec R` and each `f i` is
a group-scheme endomorphism `Spec H ⟶ Spec H`. This file defines the **fixed-point Hopf ideal**
`TauCeti.HopfIdeal.fixedPoint f = ⨆ i, HopfIdeal.equalizer (f i) (BialgHom.id R H)` and its bundled
counterparts `TauCeti.CommHopfAlgCat.fixedPointHopfIdeal` and
`TauCeti.FiniteTypeCommHopfAlgCat.fixedPointHopfIdeal`.

Because `HopfIdeal.equalizer` is a Hopf ideal and `HopfIdeal R H` is closed under arbitrary
suprema, `fixedPoint f` is automatically a Hopf ideal of `H`: the fixed locus `(Spec H)^f` is a
**closed subgroup scheme** of `Spec H`, not merely a closed subscheme. On `A`-valued points, the
subgroup cut out by `fixedPointHopfIdeal f` consists precisely of the points fixed by every
induced group endomorphism `BialgHom.mapDomain (f i).hom`
(`mem_quotientPointsSubgroup_fixedPointHopfIdeal_iff`,
`range_mapDomain_mkQuotient_fixedPointHopfIdeal`).

When a group `Θ` acts on `H` by Hopf-algebra automorphisms (`ρ : Θ →* CategoryTheory.Aut H`), the
underlying ideal of `fixedPointHopfIdeal (fun θ ↦ (ρ θ).asIso.hom)` coincides with the coordinate
fixed-point ideal `TauCeti.MulSemiringAction.fixedPointIdeal Θ H`
(`fixedPointHopfIdeal_toIdeal_eq_fixedPointIdeal`). Combining this closed-subgroup construction
with Edixhoven's coordinate-ring smoothness theorem gives **Edixhoven's tame fixed-point theorem
for affine group schemes** (`CommHopfAlgCat.smooth_quotient_fixedPointHopfIdeal`,
`FiniteTypeCommHopfAlgCat.smooth_quotient_fixedPointHopfIdeal`,
`FiniteTypeCommHopfAlgCat.exists_smooth_fixedPoints`): if `H` is smooth over `R` and
`(Nat.card Θ : R)` is invertible in `R`, then the fixed-point quotient Hopf algebra is smooth over
`R` and represents the `Θ`-fixed points on every `R`-algebra.

As an explicit sanity check (`quotientEqualizerInvMonoidAlgebraIntBialgEquiv`,
`smooth_quotient_equalizer_inv_monoidAlgebra_int_iff`), the fixed-point Hopf quotient of the
multiplicative group `𝔾ₘ = Spec R[Multiplicative ℤ]` under inversion `t ↦ t⁻¹` is isomorphic as a
bialgebra to `R[Multiplicative (ZMod 2)]` (the coordinate Hopf algebra of `μ₂`), which over a field
`k` is smooth if and only if `2` is invertible in `k`.

## Main definitions

* `TauCeti.HopfIdeal.fixedPoint`: the fixed-point Hopf ideal of a family `ι → (H →ₐc[R] H)`.
* `TauCeti.CommHopfAlgCat.fixedPointHopfIdeal` and `TauCeti.CommHopfAlgCat.liftFixedPoint`: the
  bundled fixed-point Hopf ideal in `CommHopfAlgCat R` and its coequalizer universal property.
* `TauCeti.CommHopfAlgCat.mulSemiringActionOfEnd`: the left `Θ`-action on `H` attached to a monoid
  homomorphism `Θ →* CategoryTheory.End H`.
* `TauCeti.FiniteTypeCommHopfAlgCat.fixedPointHopfIdeal`: the fixed-point Hopf ideal in
  `FiniteTypeCommHopfAlgCat R`.
* `TauCeti.HopfIdeal.quotientEqualizerInvMonoidAlgebraIntBialgEquiv`: the bialgebra isomorphism
  identifying the inversion-fixed quotient of `R[Multiplicative ℤ]` (`𝔾ₘ`) with
  `R[Multiplicative (ZMod 2)]` (`μ₂`).

## Main results

* `TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_fixedPointHopfIdeal_iff` and
  `TauCeti.CommHopfAlgCat.range_mapDomain_mkQuotient_fixedPointHopfIdeal`: point-level
  identification of the fixed-point closed subgroup.
* `TauCeti.CommHopfAlgCat.smooth_quotient_fixedPointHopfIdeal` and
  `TauCeti.FiniteTypeCommHopfAlgCat.exists_smooth_fixedPoints`: Edixhoven's theorem that fixed
  points of a group of invertible order acting on a smooth affine group scheme form a smooth closed
  subgroup scheme.
* `TauCeti.HopfIdeal.smooth_quotient_equalizer_inv_monoidAlgebra_int_iff`: over a field `k`, the
  inversion-fixed subgroup `μ₂ ⊂ 𝔾ₘ` is smooth if and only if `IsUnit (2 : k)`.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), Propositions 3.1
  and 3.4, pp. 293–295.
* J. S. Milne, *Algebraic Groups*, Cambridge University Press (2017), §1.h and §12.
-/

public section

open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom
open CategoryTheory WithConv

namespace TauCeti

universe u v w u'

namespace HopfIdeal

section FixedPoint

variable {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H] {ι : Sort w}

/-- The **fixed-point Hopf ideal** of a family `f : ι → (H →ₐc[R] H)` of bialgebra endomorphisms of
a commutative Hopf algebra `H`: the supremum of the equalizer Hopf ideals `equalizer (f i) id`.

Contravariantly, the quotient `H ⧸ (fixedPoint f).toIdeal` is the coordinate Hopf algebra of the
closed subgroup scheme of `Spec H` on which every endomorphism `Spec (f i)` restricts to the
identity. -/
def fixedPoint (f : ι → (H →ₐc[R] H)) : HopfIdeal R H :=
  ⨆ i, equalizer (f i) (BialgHom.id R H)

/-- `fixedPoint f` is the supremum of `equalizer (f i) (BialgHom.id R H)`. -/
theorem fixedPoint_def (f : ι → (H →ₐc[R] H)) :
    fixedPoint f = ⨆ i, equalizer (f i) (BialgHom.id R H) :=
  (rfl)

/-- The underlying ideal of `fixedPoint f` is the supremum of the individual displacement ideals. -/
theorem fixedPoint_toIdeal (f : ι → (H →ₐc[R] H)) :
    (fixedPoint f).toIdeal = ⨆ i, equalizerIdeal (f i) (BialgHom.id R H) := by
  simp [fixedPoint_def]

/-- Every displacement `f i a - a` lies in `fixedPoint f`. -/
theorem sub_mem_fixedPoint (f : ι → (H →ₐc[R] H)) (i : ι) (a : H) :
    f i a - a ∈ fixedPoint f := by
  rw [← mem_toIdeal, fixedPoint_toIdeal]
  exact Submodule.mem_iSup_of_mem i (sub_mem_equalizerIdeal (f i) (BialgHom.id R H) a)

/-- `(fixedPoint f).toIdeal` is the smallest ideal containing every displacement `f i a - a`. -/
theorem fixedPoint_toIdeal_le_iff {f : ι → (H →ₐc[R] H)} {J : Ideal H} :
    (fixedPoint f).toIdeal ≤ J ↔ ∀ (i : ι) (a : H), f i a - a ∈ J := by
  rw [fixedPoint_toIdeal, iSup_le_iff]
  exact forall_congr' fun _ ↦ equalizerIdeal_le_iff

/-- `fixedPoint f` is the smallest Hopf ideal containing every displacement `f i a - a`. -/
theorem fixedPoint_le_iff {f : ι → (H →ₐc[R] H)} {J : HopfIdeal R H} :
    fixedPoint f ≤ J ↔ ∀ (i : ι) (a : H), f i a - a ∈ J := by
  rw [← toIdeal_le_toIdeal, fixedPoint_toIdeal_le_iff]
  rfl

/-- A ring homomorphism out of `H` into a semiring `A` kills `(fixedPoint f).toIdeal` if and only
if it is invariant under every `f i`. -/
theorem fixedPoint_le_ker_iff {A : Type*} [Semiring A] (f : ι → (H →ₐc[R] H)) (φ : H →+* A) :
    (fixedPoint f).toIdeal ≤ RingHom.ker φ ↔ ∀ (i : ι) (a : H), φ (f i a) = φ a := by
  rw [fixedPoint_toIdeal_le_iff]
  refine forall₂_congr fun i a ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [RingHom.mem_ker] at h
    rw [← sub_add_cancel (f i a) a, map_add, h, zero_add]
  · rw [RingHom.mem_ker, sub_eq_add_neg, map_add, h, ← map_add, add_neg_cancel, map_zero]

/-- `fixedPoint f` vanishes if and only if every `f i` is the identity bialgebra morphism. -/
@[simp]
theorem fixedPoint_eq_bot_iff {f : ι → (H →ₐc[R] H)} :
    fixedPoint f = ⊥ ↔ ∀ i, f i = BialgHom.id R H := by
  rw [eq_bot_iff, fixedPoint_le_iff]
  simp only [mem_bot, sub_eq_zero, BialgHom.id_apply, DFunLike.ext_iff]

end FixedPoint

end HopfIdeal

namespace CommHopfAlgCat

section Morphisms

variable {R : Type u} [CommRing R] {H T : _root_.CommHopfAlgCat.{v} R} {ι : Sort w}

/-- The **fixed-point Hopf ideal** of a family `f : ι → (H ⟶ H)` of endomorphisms in
`CommHopfAlgCat R`. Contravariantly, `quotient H (fixedPointHopfIdeal f)` is the coordinate Hopf
algebra of the closed subgroup scheme of `Spec H` fixed by every `f i`. -/
noncomputable def fixedPointHopfIdeal (f : ι → (H ⟶ H)) : HopfIdeal R H :=
  ⨆ i, equalizerHopfIdeal (f i) (𝟙 H)

/-- `fixedPointHopfIdeal f` is the supremum of `equalizerHopfIdeal (f i) (𝟙 H)`. -/
theorem fixedPointHopfIdeal_def (f : ι → (H ⟶ H)) :
    fixedPointHopfIdeal f = ⨆ i, equalizerHopfIdeal (f i) (𝟙 H) :=
  (rfl)

/-- `fixedPointHopfIdeal f` coincides with `HopfIdeal.fixedPoint` on the underlying bialgebra
morphisms. -/
theorem fixedPointHopfIdeal_eq_fixedPoint (f : ι → (H ⟶ H)) :
    fixedPointHopfIdeal f = HopfIdeal.fixedPoint fun i ↦ (f i).hom := by
  simp_rw [fixedPointHopfIdeal_def, HopfIdeal.fixedPoint_def, equalizerHopfIdeal_def]
  rfl

/-- Every displacement `(f i).hom a - a` lies in `fixedPointHopfIdeal f`. -/
theorem sub_mem_fixedPointHopfIdeal (f : ι → (H ⟶ H)) (i : ι) (a : H) :
    (f i).hom a - a ∈ fixedPointHopfIdeal f := by
  rw [fixedPointHopfIdeal_eq_fixedPoint]
  exact HopfIdeal.sub_mem_fixedPoint (fun j ↦ (f j).hom) i a

/-- `fixedPointHopfIdeal f` is the smallest Hopf ideal containing every displacement
`(f i).hom a - a`. -/
theorem fixedPointHopfIdeal_le_iff {f : ι → (H ⟶ H)} {J : HopfIdeal R H} :
    fixedPointHopfIdeal f ≤ J ↔ ∀ (i : ι) (a : H), (f i).hom a - a ∈ J := by
  rw [fixedPointHopfIdeal_eq_fixedPoint]
  exact HopfIdeal.fixedPoint_le_iff

/-- A ring homomorphism out of `H` kills `(fixedPointHopfIdeal f).toIdeal` if and only if it is
invariant under every `(f i).hom`. -/
theorem fixedPointHopfIdeal_le_ker_iff {A : Type*} [Semiring A] (f : ι → (H ⟶ H)) (φ : H →+* A) :
    (fixedPointHopfIdeal f).toIdeal ≤ RingHom.ker φ ↔ ∀ (i : ι) (a : H), φ ((f i).hom a) = φ a := by
  rw [fixedPointHopfIdeal_eq_fixedPoint]
  exact HopfIdeal.fixedPoint_le_ker_iff (fun i ↦ (f i).hom) φ

/-- A morphism `p : H ⟶ T` kills `fixedPointHopfIdeal f` precisely when `f i ≫ p = p` for all
`i`. -/
theorem fixedPointHopfIdeal_toIdeal_le_ker_iff (f : ι → (H ⟶ H)) (p : H ⟶ T) :
    (fixedPointHopfIdeal f).toIdeal ≤ RingHom.ker p.hom.toAlgHom.toRingHom ↔
      ∀ i, f i ≫ p = p := by
  rw [fixedPointHopfIdeal_def, HopfIdeal.iSup_toIdeal, iSup_le_iff]
  exact forall_congr' fun i ↦
    (equalizerHopfIdeal_toIdeal_le_ker_iff (f i) (𝟙 H) p).trans (by rw [Category.id_comp])

/-- `fixedPointHopfIdeal f` vanishes if and only if every `f i` is `𝟙 H`. -/
@[simp]
theorem fixedPointHopfIdeal_eq_bot_iff (f : ι → (H ⟶ H)) :
    fixedPointHopfIdeal f = ⊥ ↔ ∀ i, f i = 𝟙 H := by
  rw [fixedPointHopfIdeal_eq_fixedPoint, HopfIdeal.fixedPoint_eq_bot_iff]
  exact forall_congr' fun i ↦ ⟨fun h ↦ _root_.CommHopfAlgCat.hom_ext h, fun h ↦ by rw [h]; rfl⟩

/-- The quotient morphism by `fixedPointHopfIdeal f` coequalizes every `f i` with `𝟙 H`. -/
theorem comp_mkQuotient_fixedPointHopfIdeal (f : ι → (H ⟶ H)) (i : ι) :
    f i ≫ mkQuotient H (fixedPointHopfIdeal f) = mkQuotient H (fixedPointHopfIdeal f) :=
  ((fixedPointHopfIdeal_toIdeal_le_ker_iff f (mkQuotient H (fixedPointHopfIdeal f))).mp
    (mkQuotient_ker H (fixedPointHopfIdeal f)).ge) i

/-- **Coequalizer universal property.** Any morphism `p : H ⟶ T` invariant under precomposition
with every `f i` factors through `quotient H (fixedPointHopfIdeal f)`. -/
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
    (hq : mkQuotient H (fixedPointHopfIdeal f) ≫ q = p) :
    q = liftFixedPoint p hp :=
  liftQuotient_unique _ _ _ q hq

/-- **Points of the fixed-point subgroup.** An `A`-point of `H` lies in the subgroup cut out by
`fixedPointHopfIdeal f` if and only if it is fixed by every `BialgHom.mapDomain (f i).hom`. -/
theorem mem_quotientPointsSubgroup_fixedPointHopfIdeal_iff (f : ι → (H ⟶ H))
    (A : CommAlgCat.{u'} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    x ∈ quotientPointsSubgroup H (fixedPointHopfIdeal f) A ↔
      ∀ i, BialgHom.mapDomain (f i).hom x = x := by
  rw [mem_quotientPointsSubgroup_iff]
  have hle : ((fixedPointHopfIdeal f).toIdeal ≤ RingHom.ker (x.ofConv : H →ₐ[R] A).toRingHom) ↔
      ∀ h : H, h ∈ fixedPointHopfIdeal f → x.ofConv h = 0 :=
    ⟨fun h _ hy ↦ RingHom.mem_ker.mp (h (HopfIdeal.mem_toIdeal.mpr hy)),
      fun h _ hy ↦ RingHom.mem_ker.mpr (h _ (HopfIdeal.mem_toIdeal.mp hy))⟩
  rw [← hle, fixedPointHopfIdeal_le_ker_iff]
  refine forall_congr' fun i ↦ ⟨fun h ↦ ofConv_injective (AlgHom.ext fun a ↦ ?_), fun h a ↦ ?_⟩
  · simpa only [BialgHom.mapDomain_apply_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom] using h a
  · simpa only [BialgHom.mapDomain_apply_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom] using congrArg (fun m : WithConv (H →ₐ[R] A) ↦ m.ofConv a) h

/-- The image of `(mkQuotient H (fixedPointHopfIdeal f)).hom` on `A`-valued points is the set of
points fixed under every `f i`. -/
theorem range_mapDomain_mkQuotient_fixedPointHopfIdeal (f : ι → (H ⟶ H))
    {A : Type u'} [CommRing A] [Algebra R A] :
    Set.range (BialgHom.mapDomain (A := A) (mkQuotient H (fixedPointHopfIdeal f)).hom) =
      {g | ∀ i, BialgHom.mapDomain (A := A) (f i).hom g = g} := by
  ext g
  exact mem_quotientPointsSubgroup_fixedPointHopfIdeal_iff f (CommAlgCat.of R A) g

end Morphisms

section GroupAction

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{v} R)

/-- A monoid homomorphism `ρ : Θ →* CategoryTheory.End H` induces a left action of `Θ` on `H` by
ring endomorphisms (`θ • h = (ρ θ).asHom.hom h`), because multiplication in `CategoryTheory.End H`
agrees with function composition rather than categorical diagram order. -/
@[instance_reducible]
def mulSemiringActionOfEnd {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.End H) :
    MulSemiringAction Θ H where
  smul θ h := (ρ θ).asHom.hom h
  one_smul h := congrArg (fun e : CategoryTheory.End H ↦ e.asHom.hom h) (map_one ρ)
  mul_smul θ₁ θ₂ h := congrArg (fun e : CategoryTheory.End H ↦ e.asHom.hom h) (map_mul ρ θ₁ θ₂)
  smul_zero θ := map_zero (ρ θ).asHom.hom
  smul_add θ := map_add (ρ θ).asHom.hom
  smul_one θ := map_one (ρ θ).asHom.hom
  smul_mul θ := map_mul (ρ θ).asHom.hom

/-- Under `mulSemiringActionOfEnd H ρ`, `θ • h` is `(ρ θ).asHom.hom h`. -/
@[simp]
theorem smul_mulSemiringActionOfEnd {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.End H)
    (θ : Θ) (h : H) :
    letI := mulSemiringActionOfEnd H ρ
    θ • h = (ρ θ).asHom.hom h :=
  (rfl)

/-- The `Θ`-action `mulSemiringActionOfEnd H ρ` commutes with the base `R`-action on `H`. -/
theorem smulCommClassOfEnd {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.End H) :
    letI := mulSemiringActionOfEnd H ρ
    SMulCommClass Θ R H := by
  let _ := mulSemiringActionOfEnd H ρ
  exact ⟨fun θ r h ↦ (ρ θ).asHom.hom.toAlgHom.map_smul_of_tower r h⟩

/-- For `ρ : Θ →* CategoryTheory.End H`, the underlying ideal of the fixed-point Hopf ideal
`fixedPointHopfIdeal (fun θ ↦ (ρ θ).asHom)` is `MulSemiringAction.fixedPointIdeal Θ H`. -/
theorem fixedPointHopfIdeal_toIdeal_eq_fixedPointIdeal {Θ : Type w} [Monoid Θ]
    (ρ : Θ →* CategoryTheory.End H) :
    letI := mulSemiringActionOfEnd H ρ
    (fixedPointHopfIdeal fun θ : Θ ↦ (ρ θ).asHom).toIdeal =
      MulSemiringAction.fixedPointIdeal Θ H := by
  let _ := mulSemiringActionOfEnd H ρ
  rw [fixedPointHopfIdeal_eq_fixedPoint, HopfIdeal.fixedPoint_toIdeal,
    MulSemiringAction.fixedPointIdeal_eq_iSup]
  exact iSup_congr fun θ ↦ HopfIdeal.equalizerIdeal_eq_span _ _

/-- **Edixhoven's tame fixed-point theorem for commutative Hopf algebras.** If a group `Θ` acts by
Hopf-algebra automorphisms on a smooth commutative Hopf `R`-algebra `H` and `(Nat.card Θ : R)` is
invertible in `R`, then the fixed-point quotient `quotient H (fixedPointHopfIdeal ...)` is smooth
over `R`. -/
theorem smooth_quotient_fixedPointHopfIdeal {Θ : Type w} [Group Θ]
    (hH : smoothCommHopfAlgProperty R H) (ρ : Θ →* CategoryTheory.Aut H)
    (hΘ : IsUnit (Nat.card Θ : R)) :
    smoothCommHopfAlgProperty R (quotient H (fixedPointHopfIdeal fun θ : Θ ↦ (ρ θ).asIso.hom)) := by
  rw [smoothCommHopfAlgProperty_iff] at hH ⊢
  let ρEnd : Θ →* CategoryTheory.End H := CategoryTheory.Aut.toEnd.comp ρ
  let _ : MulSemiringAction Θ H := mulSemiringActionOfEnd H ρEnd
  have _ : SMulCommClass Θ R H := smulCommClassOfEnd H ρEnd
  have hEq : (fixedPointHopfIdeal fun θ : Θ ↦ (ρ θ).asIso.hom).toIdeal =
      MulSemiringAction.fixedPointIdeal Θ H :=
    fixedPointHopfIdeal_toIdeal_eq_fixedPointIdeal H ρEnd
  have _ : Algebra.Smooth R (H ⧸ MulSemiringAction.fixedPointIdeal Θ H) :=
    MulSemiringAction.smooth_quotient_fixedPointIdeal hΘ
  exact Algebra.Smooth.of_equiv
    { Ideal.quotEquivOfEq hEq.symm with commutes' := fun _ ↦ rfl }

end GroupAction

end CommHopfAlgCat

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [CommRing k]

/-- The **fixed-point Hopf ideal** of a family `f : ι → (H ⟶ H)` of endomorphisms in
`FiniteTypeCommHopfAlgCat k`. -/
noncomputable def fixedPointHopfIdeal {H : FiniteTypeCommHopfAlgCat.{u, v} k} {ι : Sort w}
    (f : ι → (H ⟶ H)) : HopfIdeal k H :=
  CommHopfAlgCat.fixedPointHopfIdeal fun i ↦ (f i).hom

/-- Explicit unfolding of `FiniteTypeCommHopfAlgCat.fixedPointHopfIdeal` in terms of
`CommHopfAlgCat.fixedPointHopfIdeal`. -/
theorem fixedPointHopfIdeal_def {H : FiniteTypeCommHopfAlgCat.{u, v} k} {ι : Sort w}
    (f : ι → (H ⟶ H)) :
    fixedPointHopfIdeal f = CommHopfAlgCat.fixedPointHopfIdeal fun i ↦ (f i).hom :=
  (rfl)

/-- On `R`-valued points, the image of `mkQuotient H (fixedPointHopfIdeal f)` is the set of points
fixed under every `f i`. -/
theorem range_mapDomain_mkQuotient_fixedPointHopfIdeal {H : FiniteTypeCommHopfAlgCat.{u, v} k}
    {ι : Sort w} (f : ι → (H ⟶ H)) {R : Type u'} [CommRing R] [Algebra k R] :
    Set.range (BialgHom.mapDomain (A := R) (toBialgHom (mkQuotient H (fixedPointHopfIdeal f)))) =
      {g | ∀ i, BialgHom.mapDomain (A := R) (toBialgHom (f i)) g = g} :=
  CommHopfAlgCat.range_mapDomain_mkQuotient_fixedPointHopfIdeal (fun i ↦ (f i).hom)

/-- **Edixhoven's theorem for `FiniteTypeCommHopfAlgCat` (explicit quotient form).** For a group `Θ`
of invertible order acting on a smooth finite-type commutative Hopf `k`-algebra `H`, the explicit
fixed-point quotient `quotient H (fixedPointHopfIdeal ...)` is smooth over `k`. -/
theorem smooth_quotient_fixedPointHopfIdeal (H : FiniteTypeCommHopfAlgCat.{u, v} k)
    (hH : smoothCommHopfAlgProperty k H.obj) {Θ : Type w} [Group Θ]
    (ρ : Θ →* CategoryTheory.Aut H) (hΘ : IsUnit (Nat.card Θ : k)) :
    smoothCommHopfAlgProperty k
      (quotient H (fixedPointHopfIdeal fun θ : Θ ↦ (ρ θ).asIso.hom)).obj := by
  let forgetAut : CategoryTheory.Aut H →* CategoryTheory.Aut H.obj :=
    { toFun e := .of ((forget₂ (FiniteTypeCommHopfAlgCat.{u, v} k)
        (_root_.CommHopfAlgCat.{v} k)).mapIso e.asIso)
      map_one' := by ext; rfl
      map_mul' _ _ := by ext; rfl }
  exact CommHopfAlgCat.smooth_quotient_fixedPointHopfIdeal H.obj hH (forgetAut.comp ρ) hΘ

/-- **Edixhoven's tame fixed-point theorem for finite-type affine group schemes.** Let a group `Θ`
act on `H : FiniteTypeCommHopfAlgCat k` with `H` smooth over `k` and `(Nat.card Θ : k)` invertible
in `k`. Then there exists a smooth `H' : FiniteTypeCommHopfAlgCat k` and a surjective morphism
`f : H ⟶ H'` whose induced map on `R`-valued points has range equal to the `Θ`-fixed subgroup for
every commutative `k`-algebra `R`. -/
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

end FiniteTypeCommHopfAlgCat

namespace HopfIdeal

section MultiplicativeGroupInversion

/-- **The fixed-point ideal of inversion on `𝔾ₘ` is `(T² - 1)`.** On the coordinate Hopf algebra
`MonoidAlgebra R (Multiplicative ℤ)` of `𝔾ₘ`, the equalizer Hopf ideal of the inversion
endomorphism `ofAdd k ↦ ofAdd (-k)` with the identity has underlying ideal generated by
`single (ofAdd 2) 1 - 1`, matching the defining ideal of `μ₂ ⊂ 𝔾ₘ`. -/
theorem equalizer_inv_monoidAlgebra_int_toIdeal (R : Type u) [CommRing R] :
    (equalizer
        (MonoidAlgebra.mapDomainBialgHom R (MulEquiv.inv (Multiplicative ℤ)).toMonoidHom)
        (BialgHom.id R (MonoidAlgebra R (Multiplicative ℤ)))).toIdeal =
      Ideal.span {MonoidAlgebra.single (Multiplicative.ofAdd (2 : ℤ)) (1 : R) - 1} := by
  let invHom := MonoidAlgebra.mapDomainBialgHom R (MulEquiv.inv (Multiplicative ℤ)).toMonoidHom
  have hker := RootsOfUnityGroup.ker_mapDomainRingHom_toMultiplicativeZMod R 2
  norm_num at hker
  rw [← hker]
  refine le_antisymm ?_ ?_
  · rw [equalizer_le_ker_iff]
    intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add y z hy hz => rw [map_add, map_add, map_add, map_add, hy, hz]
    | single m r =>
      induction m using Multiplicative.rec with | ofAdd k => ?_
      rw [MonoidAlgebra.mapDomainBialgHom_single, BialgHom.id_apply]
      simp [← ofAdd_neg, ZMod.neg_eq_self_mod_two]
  · rw [hker, Ideal.span_singleton_le_iff_mem]
    have hmem : invHom (MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : R)) -
        MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : R) ∈
        (equalizer invHom (BialgHom.id R _)).toIdeal :=
      sub_mem_equalizer (MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : R))
    have hmul := (equalizer invHom (BialgHom.id R _)).toIdeal.mul_mem_left
      (-MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : R)) hmem
    have hcalc : -MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : R) *
          (invHom (MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : R)) -
            MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : R)) =
        MonoidAlgebra.single (Multiplicative.ofAdd (2 : ℤ)) (1 : R) - 1 := by
      dsimp only [invHom]
      have hinv : (MulEquiv.inv (Multiplicative ℤ)).toMonoidHom (Multiplicative.ofAdd (1 : ℤ)) =
          Multiplicative.ofAdd (-1 : ℤ) := by
        simp [← ofAdd_neg]
      rw [MonoidAlgebra.mapDomainBialgHom_single, hinv, neg_mul, mul_sub,
        MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single,
        ← ofAdd_add, ← ofAdd_add]
      norm_num
      rw [MonoidAlgebra.one_def]
    rwa [hcalc] at hmul

/-- The equalizer Hopf ideal of inversion on `𝔾ₘ` equals the kernel Hopf ideal of the canonical
coordinate surjection `R[Multiplicative ℤ] ↠ R[Multiplicative (ZMod 2)]`. -/
theorem equalizer_inv_monoidAlgebra_int_eq_kerOfSurjective (R : Type u) [CommRing R] :
    equalizer
        (MonoidAlgebra.mapDomainBialgHom R (MulEquiv.inv (Multiplicative ℤ)).toMonoidHom)
        (BialgHom.id R (MonoidAlgebra R (Multiplicative ℤ))) =
      kerOfSurjective (MonoidAlgebra.mapDomainBialgHom R (RootsOfUnityGroup.toMultiplicativeZMod 2))
        (_root_.MonoidAlgebra.mapDomain_surjective
          (RootsOfUnityGroup.toMultiplicativeZMod_surjective 2)) := by
  have hker := RootsOfUnityGroup.ker_mapDomainRingHom_toMultiplicativeZMod R 2
  norm_num at hker
  have hEq : (equalizer
        (MonoidAlgebra.mapDomainBialgHom R (MulEquiv.inv (Multiplicative ℤ)).toMonoidHom)
        (BialgHom.id R (MonoidAlgebra R (Multiplicative ℤ)))).toIdeal =
      (kerOfSurjective
        (MonoidAlgebra.mapDomainBialgHom R (RootsOfUnityGroup.toMultiplicativeZMod 2))
        (_root_.MonoidAlgebra.mapDomain_surjective
          (RootsOfUnityGroup.toMultiplicativeZMod_surjective 2))).toIdeal :=
    (equalizer_inv_monoidAlgebra_int_toIdeal R).trans <| hker.symm.trans <|
      (congrArg RingHom.ker
        (MonoidAlgebra.mapDomainBialgHom_toRingHom R
          (RootsOfUnityGroup.toMultiplicativeZMod 2)).symm).trans
        (kerOfSurjective_toIdeal _ _).symm
  exact le_antisymm (toIdeal_le_toIdeal.mp hEq.le) (toIdeal_le_toIdeal.mp hEq.ge)

/-- **Fixed-point subgroup of `𝔾ₘ` under inversion is `μ₂`.** Quotienting
`MonoidAlgebra R (Multiplicative ℤ)` by the equalizer Hopf ideal of inversion gives a bialgebra
canonically isomorphic to `MonoidAlgebra R (Multiplicative (ZMod 2))`. -/
noncomputable def quotientEqualizerInvMonoidAlgebraIntBialgEquiv (R : Type u) [CommRing R] :
    (MonoidAlgebra R (Multiplicative ℤ) ⧸
        (equalizer
          (MonoidAlgebra.mapDomainBialgHom R (MulEquiv.inv (Multiplicative ℤ)).toMonoidHom)
          (BialgHom.id R (MonoidAlgebra R (Multiplicative ℤ)))).toIdeal) ≃ₐc[R]
      MonoidAlgebra R (Multiplicative (ZMod 2)) :=
  _root_.CommHopfAlgCat.ofIso
    (CommHopfAlgCat.Hom.quotientIsoOfKerOfSurjectiveEq
      (H := _root_.CommHopfAlgCat.of R (MonoidAlgebra R (Multiplicative ℤ)))
      (K := _root_.CommHopfAlgCat.of R (MonoidAlgebra R (Multiplicative (ZMod 2))))
      (_root_.CommHopfAlgCat.ofHom
        (MonoidAlgebra.mapDomainBialgHom R (RootsOfUnityGroup.toMultiplicativeZMod 2)))
      (_root_.MonoidAlgebra.mapDomain_surjective
        (RootsOfUnityGroup.toMultiplicativeZMod_surjective 2))
      (equalizer_inv_monoidAlgebra_int_eq_kerOfSurjective R).symm)

/-- When `2` is invertible in `R`, the inversion-fixed quotient of `𝔾ₘ` is étale (hence smooth)
over `R`. -/
theorem etale_quotient_equalizer_inv_monoidAlgebra_int (R : Type u) [CommRing R]
    (h2 : IsUnit (2 : R)) :
    Algebra.Etale R
      (MonoidAlgebra R (Multiplicative ℤ) ⧸
        (equalizer
          (MonoidAlgebra.mapDomainBialgHom R (MulEquiv.inv (Multiplicative ℤ)).toMonoidHom)
          (BialgHom.id R (MonoidAlgebra R (Multiplicative ℤ)))).toIdeal) := by
  have hcard : Nat.card (Multiplicative (ZMod 2)) = 2 :=
    (Nat.card_congr (Multiplicative.ofAdd : ZMod 2 ≃ Multiplicative (ZMod 2))).trans
      (Nat.card_zmod 2)
  have _ : Algebra.Etale R (MonoidAlgebra R (Multiplicative (ZMod 2))) :=
    MonoidAlgebra.etale_of_isUnit_card R (Multiplicative (ZMod 2)) (by simpa [hcard] using h2)
  exact Algebra.Etale.of_equiv (quotientEqualizerInvMonoidAlgebraIntBialgEquiv R).symm.toAlgEquiv

/-- **Sharpness of tameness for inversion on `𝔾ₘ`.** Over a field `k`, the inversion-fixed subgroup
quotient of `𝔾ₘ` (`μ₂`) is smooth over `k` if and only if `2` is invertible in `k`. -/
theorem smooth_quotient_equalizer_inv_monoidAlgebra_int_iff (k : Type u) [Field k] :
    Algebra.Smooth k
      (MonoidAlgebra k (Multiplicative ℤ) ⧸
        (equalizer
          (MonoidAlgebra.mapDomainBialgHom k (MulEquiv.inv (Multiplicative ℤ)).toMonoidHom)
          (BialgHom.id k (MonoidAlgebra k (Multiplicative ℤ)))).toIdeal) ↔
      IsUnit (2 : k) := by
  have hcard : Nat.card (Multiplicative (ZMod 2)) = 2 :=
    (Nat.card_congr (Multiplicative.ofAdd : ZMod 2 ≃ Multiplicative (ZMod 2))).trans
      (Nat.card_zmod 2)
  let e := (quotientEqualizerInvMonoidAlgebraIntBialgEquiv k).toAlgEquiv
  refine ⟨fun hs ↦ ?_, fun h2 ↦ ?_⟩
  · have hs' : Algebra.Smooth k (MonoidAlgebra k (Multiplicative (ZMod 2))) :=
      Algebra.Smooth.of_equiv e
    simpa [hcard] using
      (MonoidAlgebra.smooth_iff_isUnit_card k (Multiplicative (ZMod 2))).mp hs'
  · have _ := etale_quotient_equalizer_inv_monoidAlgebra_int k h2
    infer_instance

end MultiplicativeGroupInversion

end HopfIdeal

end TauCeti
