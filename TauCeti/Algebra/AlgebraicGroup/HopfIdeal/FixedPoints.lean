/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Equalizer
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import TauCeti.Algebra.HopfAlgebra.Antipode
public import TauCeti.RingTheory.Idempotents.Connected.Spectrum
public import TauCeti.RingTheory.Smooth.FixedPoints

/-!
# Fixed-point closed subgroup schemes and Edixhoven's smoothness theorem for affine groups

Let a family of group-scheme endomorphisms act on an affine group scheme `G = Spec H` over a
commutative ring `R` — contravariantly, let `f : ι → (H ⟶ H)` be a family of endomorphisms in
`CommHopfAlgCat R`. The **fixed-point Hopf ideal** `fixedPointHopfIdeal f` is the supremum of the
equalizer Hopf ideals `equalizerHopfIdeal (f i) (𝟙 H)`. Because suprema and equalizers of Hopf
ideals are Hopf ideals, the quotient `quotient H (fixedPointHopfIdeal f)` is a commutative Hopf
algebra representing a *closed subgroup scheme* `G^f ⊆ G` whose `A`-points are the `A`-points of
`G` fixed by every `f i` (`mem_quotientPointsSubgroup_fixedPointHopfIdeal_iff`,
`range_mapDomain_mkQuotient_fixedPointHopfIdeal`).

When a finite group `Θ` of order invertible in `R` acts on a smooth commutative Hopf algebra `H` by
Hopf-algebra automorphisms `ρ : Θ →* CategoryTheory.Aut H`, the underlying ideal of
`fixedPointHopfIdeal` coincides with `TauCeti.MulSemiringAction.fixedPointIdeal Θ H`. Edixhoven's
smoothness theorem (`TauCeti.MulSemiringAction.smooth_quotient_fixedPointIdeal`) therefore makes the
fixed-point closed subgroup scheme smooth over `R`
(`CommHopfAlgCat.smoothCommHopfAlgProperty_quotient_fixedPointHopfIdeal`,
`FiniteTypeCommHopfAlgCat.smoothCommHopfAlgProperty_fixedPoints`,
`FiniteTypeCommHopfAlgCat.exists_smooth_fixedPoints`).

We also record three concrete computations illustrating the behaviour of fixed-point subgroup
schemes:
* Trivial actions have vanishing fixed-point Hopf ideal and leave the group unchanged
  (`FiniteTypeCommHopfAlgCat.fixedPointsIsoOfEqOne`).
* On the product `G × G` (`H ⊗[R] H`), the fixed-point subgroup of the factor-swapping involution
  is isomorphic to the diagonal `G` via multiplication (`CommHopfAlgCat.quotientSwapEqualizerIso`).
* On `𝔾ₘ = Spec R[T;T⁻¹]`, the fixed-point subgroup of inversion cuts out the `2`-torsion units
  `{u ∈ Aˣ | u ^ 2 = 1}` (`CommHopfAlgCat.mem_quotientPointsSubgroup_inversion_iff`), and when
  `2 ∈ Rˣ` over a nontrivial base ring its prime spectrum is disconnected
  (`HopfIdeal.not_connectedSpace_primeSpectrum_quotient_multiplicativeGroupInversion`), showing
  that tame fixed-point schemes of connected smooth groups remain smooth without remaining
  connected.

## Main definitions

* `TauCeti.HopfIdeal.fixedPoints`: the Hopf ideal `⨆ i, equalizer (f i) (BialgHom.id R H)` of a
  family of bialgebra endomorphisms of a commutative Hopf algebra.
* `TauCeti.CommHopfAlgCat.fixedPointHopfIdeal` and `TauCeti.CommHopfAlgCat.liftFixedPoints`: the
  categorical fixed-point Hopf ideal and its universal property.
* `TauCeti.FiniteTypeCommHopfAlgCat.fixedPoints` and
  `TauCeti.FiniteTypeCommHopfAlgCat.mkFixedPoints`: the fixed-point quotient object and quotient
  morphism in `FiniteTypeCommHopfAlgCat R` for `ρ : Θ →* CategoryTheory.Aut H`.
* `TauCeti.CommHopfAlgCat.quotientSwapEqualizerIso`: diagonal identification for the swap
  involution on `H ⊗[R] H`.
* `TauCeti.HopfIdeal.multiplicativeGroupInversion`: the fixed-point Hopf ideal of inversion on
  `R[T;T⁻¹]`.

## Main results

* `TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_fixedPointHopfIdeal_iff` and
  `TauCeti.FiniteTypeCommHopfAlgCat.range_mapDomain_mkFixedPoints`: characterization of `A`-points
  of the fixed-point closed subgroup scheme.
* `TauCeti.FiniteTypeCommHopfAlgCat.smoothCommHopfAlgProperty_fixedPoints` and
  `TauCeti.FiniteTypeCommHopfAlgCat.exists_smooth_fixedPoints`: Edixhoven's theorem for smooth
  affine group schemes of finite type under finite groups of invertible order.
* `TauCeti.HopfIdeal.not_connectedSpace_primeSpectrum_quotient_multiplicativeGroupInversion`:
  non-connectedness of `(𝔾ₘ)^{inv} = μ₂` when `2` is invertible in a nontrivial base ring.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), Propositions 3.1
  and 3.4, pp. 293–295.
* J. S. Milne, *Algebraic Groups* (2017), §1.h.
-/

public section

open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom
open CategoryTheory WithConv
open scoped TensorProduct LaurentPolynomial

namespace TauCeti

universe u v w x

namespace HopfIdeal

section General

variable {R : Type u} [CommRing R] {H : Type v} [CommRing H] [_root_.HopfAlgebra R H]
  {ι : Type w}

/-- The **fixed-point Hopf ideal** of a family `f : ι → (H →ₐc[R] H)` of bialgebra endomorphisms of
a commutative Hopf algebra: the supremum of the equalizer Hopf ideals
`equalizer (f i) (BialgHom.id R H)`. Contravariantly, `H ⧸ (fixedPoints f).toIdeal` is the
coordinate Hopf algebra of the closed subgroup scheme of points fixed by every `f i`. -/
noncomputable def fixedPoints (f : ι → (H →ₐc[R] H)) : HopfIdeal R H :=
  ⨆ i, equalizer (f i) (BialgHom.id R H)

/-- `fixedPoints f` is the supremum of the individual equalizer Hopf ideals with the identity. -/
theorem fixedPoints_eq_iSup (f : ι → (H →ₐc[R] H)) :
    fixedPoints f = ⨆ i, equalizer (f i) (BialgHom.id R H) :=
  (rfl)

/-- The ideal underlying `fixedPoints f` is spanned by all displacements `f i a - a`. -/
theorem fixedPoints_toIdeal (f : ι → (H →ₐc[R] H)) :
    (fixedPoints f).toIdeal = Ideal.span {y : H | ∃ (i : ι) (a : H), f i a - a = y} := by
  rw [fixedPoints_eq_iSup, iSup_toIdeal]
  apply le_antisymm
  · refine iSup_le fun i ↦ ?_
    rw [equalizer_toIdeal, equalizerIdeal_le_iff]
    exact fun a ↦ Ideal.subset_span ⟨i, a, rfl⟩
  · rw [Ideal.span_le]
    rintro _ ⟨i, a, rfl⟩
    have hsub := sub_mem_equalizerIdeal (f i) (BialgHom.id R H) a
    rw [BialgHom.id_apply, ← equalizer_toIdeal] at hsub
    exact Submodule.mem_iSup_of_mem i hsub

/-- When a type `G` acts on `H` through a family of bialgebra endomorphisms `f`, the ideal
underlying `HopfIdeal.fixedPoints f` coincides with `MulSemiringAction.fixedPointIdeal G H`. -/
theorem fixedPoints_toIdeal_eq_fixedPointIdeal {G : Type w} [SMul G H] (f : G → (H →ₐc[R] H))
    (hf : ∀ (g : G) (a : H), g • a = f g a) :
    (fixedPoints f).toIdeal = MulSemiringAction.fixedPointIdeal G H := by
  rw [fixedPoints_toIdeal, MulSemiringAction.fixedPointIdeal_def]
  simp_rw [hf]

/-- Every displacement `f i a - a` belongs to `fixedPoints f`. -/
theorem sub_mem_fixedPoints (f : ι → (H →ₐc[R] H)) (i : ι) (a : H) :
    f i a - a ∈ fixedPoints f := by
  rw [← mem_toIdeal, fixedPoints_toIdeal]
  exact Ideal.subset_span ⟨i, a, rfl⟩

/-- Universal property of `fixedPoints f` among Hopf ideals of `H`. -/
theorem fixedPoints_le_iff {f : ι → (H →ₐc[R] H)} {J : HopfIdeal R H} :
    fixedPoints f ≤ J ↔ ∀ (i : ι) (a : H), f i a - a ∈ J := by
  rw [← toIdeal_le_toIdeal, fixedPoints_eq_iSup, iSup_toIdeal, iSup_le_iff]
  exact forall_congr' fun i ↦ by
    rw [toIdeal_le_toIdeal, equalizer_le_iff]
    simp only [BialgHom.id_apply]

/-- A ring homomorphism out of `H` kills `fixedPoints f` if and only if it equalizes every `f i`
with the identity. -/
theorem fixedPoints_le_ker_iff {A : Type*} [Ring A] (f : ι → (H →ₐc[R] H)) (φ : H →+* A) :
    (fixedPoints f).toIdeal ≤ RingHom.ker φ ↔ ∀ (i : ι) (a : H), φ (f i a) = φ a := by
  rw [fixedPoints_eq_iSup, iSup_toIdeal, iSup_le_iff]
  exact forall_congr' fun _ ↦ equalizer_le_ker_iff φ

/-- `fixedPoints f` vanishes if and only if every `f i` is the identity bialgebra morphism. -/
@[simp]
theorem fixedPoints_eq_bot_iff (f : ι → (H →ₐc[R] H)) :
    fixedPoints f = ⊥ ↔ ∀ i, f i = BialgHom.id R H := by
  rw [eq_bot_iff, fixedPoints_le_iff]
  simp only [mem_bot, sub_eq_zero, BialgHom.ext_iff, BialgHom.id_apply]

end General

section MultiplicativeGroupInversion

/-- The fixed-point Hopf ideal of inversion (`HopfAlgebra.antipodeBialgHom`) on `R[T;T⁻¹]`,
cutting out the `2`-torsion closed subgroup `μ₂ ⊆ 𝔾ₘ`. -/
noncomputable def multiplicativeGroupInversion (R : Type u) [CommRing R] : HopfIdeal R R[T;T⁻¹] :=
  equalizer (HopfAlgebra.antipodeBialgHom (R := R) (A := R[T;T⁻¹])) (BialgHom.id R R[T;T⁻¹])

theorem multiplicativeGroupInversion_def (R : Type u) [CommRing R] :
    multiplicativeGroupInversion R =
      equalizer (HopfAlgebra.antipodeBialgHom (R := R) (A := R[T;T⁻¹]))
        (BialgHom.id R R[T;T⁻¹]) :=
  (rfl)

/-- Every `2`-torsion unit `u : Rˣ` (`u⁻¹ = u`) defines an `R`-algebra evaluation on `R[T;T⁻¹]`
that vanishes on `multiplicativeGroupInversion R`. -/
private theorem multiplicativeGroupInversion_le_ker_laurentEval {R : Type u} [CommRing R]
    {u : Rˣ} (hu : u⁻¹ = u) :
    (multiplicativeGroupInversion R).toIdeal ≤ RingHom.ker (laurentEval (R := R) u).toRingHom := by
  rw [multiplicativeGroupInversion_def, equalizer_le_ker_iff]
  have heq : (laurentEval (R := R) u).comp (_root_.HopfAlgebra.antipodeAlgHom R R[T;T⁻¹]) =
      laurentEval (R := R) u := by
    apply laurentEval_unique
    simp [zpow_neg, hu]
  intro p
  simpa only [HopfAlgebra.antipodeBialgHom_apply, BialgHom.id_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, AlgHom.comp_apply, _root_.HopfAlgebra.antipodeAlgHom_apply] using
    congr($heq p)

/-- Modulo `multiplicativeGroupInversion R`, the coordinate `T 1` squares to `1`. -/
private theorem mk_T_mul_self_multiplicativeGroupInversion (R : Type u) [CommRing R] :
    let I := (multiplicativeGroupInversion R).toIdeal
    Ideal.Quotient.mk I (LaurentPolynomial.T 1) *
      Ideal.Quotient.mk I (LaurentPolynomial.T 1) = 1 := by
  intro I
  have ht_inv : Ideal.Quotient.mk I (LaurentPolynomial.T (-1)) =
      Ideal.Quotient.mk I (LaurentPolynomial.T 1) := by
    apply Ideal.Quotient.eq.mpr
    have hmem : (HopfAlgebra.antipodeBialgHom (R := R) (A := R[T;T⁻¹])) (LaurentPolynomial.T 1) -
        (BialgHom.id R R[T;T⁻¹]) (LaurentPolynomial.T 1) ∈ I :=
      mem_toIdeal.mpr (sub_mem_equalizer (LaurentPolynomial.T 1))
    simpa only [HopfAlgebra.antipodeBialgHom_apply, LaurentPolynomial.antipode_T,
      BialgHom.id_apply] using hmem
  calc
    Ideal.Quotient.mk I (LaurentPolynomial.T 1) * Ideal.Quotient.mk I (LaurentPolynomial.T 1)
        = Ideal.Quotient.mk I (LaurentPolynomial.T 1) *
            Ideal.Quotient.mk I (LaurentPolynomial.T (-1)) := by rw [ht_inv]
    _ = Ideal.Quotient.mk I (LaurentPolynomial.T 1 * LaurentPolynomial.T (-1)) :=
          (map_mul _ _ _).symm
    _ = 1 := by rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero, map_one]

/-- Over a nontrivial base ring `R` in which `2` is invertible, the fixed-point quotient of
`R[T;T⁻¹]` under inversion has a nontrivial idempotent `(1/2) • (1 + T)` and hence a disconnected
prime spectrum. Smooth fixed-point subgroup schemes of connected smooth groups need not be
connected. -/
theorem not_connectedSpace_primeSpectrum_quotient_multiplicativeGroupInversion
    {R : Type u} [CommRing R] [Nontrivial R] (h2 : IsUnit (2 : R)) :
    ¬ ConnectedSpace
      (PrimeSpectrum (R[T;T⁻¹] ⧸ (multiplicativeGroupInversion R).toIdeal)) := by
  intro hconn
  let I : Ideal R[T;T⁻¹] := (multiplicativeGroupInversion R).toIdeal
  let c : R := ↑h2.unit⁻¹
  have hc2 : c * 2 = 1 := Units.inv_mul_eq_one.mpr rfl
  let t : R[T;T⁻¹] ⧸ I := Ideal.Quotient.mk I (LaurentPolynomial.T 1)
  have ht : t * t = 1 := mk_T_mul_self_multiplicativeGroupInversion R
  let e : R[T;T⁻¹] ⧸ I := Ideal.Quotient.mkₐ R I (c • (1 + LaurentPolynomial.T 1))
  have he : IsIdempotentElem e := by
    have he_eq : e = algebraMap R _ c * (1 + t) := by
      simp [e, t, Algebra.smul_def, Ideal.Quotient.mkₐ_eq_mk]
    change e * e = e
    rw [he_eq, ← sub_eq_zero]
    calc
      algebraMap R _ c * (1 + t) * (algebraMap R _ c * (1 + t)) - algebraMap R _ c * (1 + t)
          = algebraMap R _ c * ((algebraMap R _ c * 2 - 1) * (1 + t) +
              algebraMap R _ c * (t * t - 1)) := by ring
      _ = 0 := by
            rw [← map_ofNat (algebraMap R _), ← map_mul, hc2, map_one, ht, sub_self,
              zero_mul, mul_zero, add_zero, mul_zero]
  rcases he.eq_zero_or_eq_one_of_preconnectedSpace with he0 | he1
  · let φpos : (R[T;T⁻¹] ⧸ I) →ₐ[R] R :=
      Ideal.Quotient.liftₐ I (laurentEval (R := R) (1 : Rˣ)) fun _ hx ↦
        RingHom.mem_ker.mp (multiplicativeGroupInversion_le_ker_laurentEval inv_one hx)
    have hφ : φpos e = 1 := by
      have h1 : φpos e = laurentEval (R := R) (1 : Rˣ) (c • (1 + LaurentPolynomial.T 1)) := rfl
      rw [h1, map_smul, map_add, map_one, laurentEval_T]
      simp only [Units.val_one, one_zpow, smul_eq_mul]
      exact (show c * (1 + 1) = c * 2 by ring).trans hc2
    rw [he0, map_zero] at hφ
    exact zero_ne_one hφ
  · let φneg : (R[T;T⁻¹] ⧸ I) →ₐ[R] R :=
      Ideal.Quotient.liftₐ I (laurentEval (R := R) (-1 : Rˣ)) fun _ hx ↦
        RingHom.mem_ker.mp
          (multiplicativeGroupInversion_le_ker_laurentEval (Units.ext (by simp)) hx)
    have hφ : φneg e = 0 := by
      have h1 : φneg e = laurentEval (R := R) (-1 : Rˣ) (c • (1 + LaurentPolynomial.T 1)) := rfl
      rw [h1]
      simp
    rw [he1, map_one] at hφ
    exact one_ne_zero hφ

end MultiplicativeGroupInversion

end HopfIdeal

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

section Categorical

variable {H T : _root_.CommHopfAlgCat.{v} R} {ι : Type w}

/-- The **fixed-point Hopf ideal** of a family `f : ι → (H ⟶ H)` of endomorphisms in
`CommHopfAlgCat R`. Contravariantly, its quotient represents the closed subgroup scheme of `Spec H`
fixed by every endomorphism in the family. -/
noncomputable def fixedPointHopfIdeal (f : ι → (H ⟶ H)) : HopfIdeal R H :=
  HopfIdeal.fixedPoints fun i ↦ (f i).hom

/-- `fixedPointHopfIdeal f` is the supremum of `equalizerHopfIdeal (f i) (𝟙 H)`. -/
theorem fixedPointHopfIdeal_eq_iSup (f : ι → (H ⟶ H)) :
    fixedPointHopfIdeal f = ⨆ i, equalizerHopfIdeal (f i) (𝟙 H) := by
  simp only [fixedPointHopfIdeal, HopfIdeal.fixedPoints_eq_iSup, equalizerHopfIdeal_def]
  rfl

/-- A morphism `p : H ⟶ T` kills `fixedPointHopfIdeal f` if and only if it coequalizes every `f i`
with `𝟙 H`. -/
theorem fixedPointHopfIdeal_toIdeal_le_ker_iff (f : ι → (H ⟶ H)) (p : H ⟶ T) :
    (fixedPointHopfIdeal f).toIdeal ≤ RingHom.ker p.hom.toAlgHom.toRingHom ↔
      ∀ i, f i ≫ p = p := by
  rw [fixedPointHopfIdeal_eq_iSup, HopfIdeal.iSup_toIdeal, iSup_le_iff]
  refine forall_congr' fun i ↦ ?_
  simpa only [Category.id_comp] using equalizerHopfIdeal_toIdeal_le_ker_iff (f i) (𝟙 H) p

/-- `fixedPointHopfIdeal f` vanishes if and only if every `f i` is the identity morphism. -/
@[simp]
theorem fixedPointHopfIdeal_eq_bot_iff (f : ι → (H ⟶ H)) :
    fixedPointHopfIdeal f = ⊥ ↔ ∀ i, f i = 𝟙 H := by
  rw [fixedPointHopfIdeal, HopfIdeal.fixedPoints_eq_bot_iff]
  exact forall_congr' fun i ↦ ⟨fun h ↦ _root_.CommHopfAlgCat.hom_ext h, fun h ↦ by rw [h]; rfl⟩

/-- The quotient morphism `H ⟶ quotient H (fixedPointHopfIdeal f)` coequalizes every `f i` with
`𝟙 H`. -/
theorem comp_mkQuotient_fixedPointHopfIdeal (f : ι → (H ⟶ H)) (i : ι) :
    f i ≫ mkQuotient H (fixedPointHopfIdeal f) = mkQuotient H (fixedPointHopfIdeal f) :=
  ((fixedPointHopfIdeal_toIdeal_le_ker_iff f
    (mkQuotient H (fixedPointHopfIdeal f))).mp (mkQuotient_ker H _).ge) i

/-- Universal property of the fixed-point quotient in `CommHopfAlgCat R`: any morphism `p : H ⟶ T`
satisfying `f i ≫ p = p` for all `i` factors through `quotient H (fixedPointHopfIdeal f)`. -/
noncomputable def liftFixedPoints {f : ι → (H ⟶ H)} (p : H ⟶ T) (hp : ∀ i, f i ≫ p = p) :
    quotient H (fixedPointHopfIdeal f) ⟶ T :=
  liftQuotient (fixedPointHopfIdeal f) p ((fixedPointHopfIdeal_toIdeal_le_ker_iff f p).mpr hp)

@[simp]
theorem mkQuotient_comp_liftFixedPoints {f : ι → (H ⟶ H)} (p : H ⟶ T)
    (hp : ∀ i, f i ≫ p = p) :
    mkQuotient H (fixedPointHopfIdeal f) ≫ liftFixedPoints p hp = p :=
  mkQuotient_comp_liftQuotient _ _ _

theorem liftFixedPoints_unique {f : ι → (H ⟶ H)} (p : H ⟶ T) (hp : ∀ i, f i ≫ p = p)
    (q : quotient H (fixedPointHopfIdeal f) ⟶ T)
    (hq : mkQuotient H (fixedPointHopfIdeal f) ≫ q = p) :
    q = liftFixedPoints p hp :=
  liftQuotient_unique _ _ _ q hq

/-- On `A`-points, the closed subgroup cut out by `fixedPointHopfIdeal f` consists of those points
fixed by every `BialgHom.mapDomain (f i).hom`. -/
theorem mem_quotientPointsSubgroup_fixedPointHopfIdeal_iff (f : ι → (H ⟶ H))
    (A : CommAlgCat.{x} R) (g : HopfAlgebra.points (R := R) (H := H) A) :
    g ∈ quotientPointsSubgroup H (fixedPointHopfIdeal f) A ↔
      ∀ i, BialgHom.mapDomain (f i).hom g = g := by
  rw [mem_quotientPointsSubgroup_iff]
  have hle : ((fixedPointHopfIdeal f).toIdeal ≤
      RingHom.ker (g.ofConv : H →ₐ[R] A).toRingHom) ↔
      ∀ h : H, h ∈ fixedPointHopfIdeal f → g.ofConv h = 0 :=
    ⟨fun h _ hy ↦ RingHom.mem_ker.mp (h (HopfIdeal.mem_toIdeal.mpr hy)),
      fun h _ hy ↦ RingHom.mem_ker.mpr (h _ (HopfIdeal.mem_toIdeal.mp hy))⟩
  rw [← hle, fixedPointHopfIdeal, HopfIdeal.fixedPoints_le_ker_iff]
  refine forall_congr' fun i ↦ ⟨fun h ↦ ?_, fun h a ↦ ?_⟩
  · apply WithConv.ofConv_injective
    ext a
    simpa only [BialgHom.mapDomain_apply_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom] using h a
  · simpa only [BialgHom.mapDomain_apply_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom] using congrArg (fun m : WithConv (H →ₐ[R] A) ↦ m.ofConv a) h

/-- Image-of-`mapDomain` form of `mem_quotientPointsSubgroup_fixedPointHopfIdeal_iff`: for every
commutative `R`-algebra `A`, the `A`-points of `quotient H (fixedPointHopfIdeal f)` map onto the
subset of `A`-points of `H` fixed by every `f i`. -/
theorem range_mapDomain_mkQuotient_fixedPointHopfIdeal (f : ι → (H ⟶ H))
    (A : Type x) [CommRing A] [Algebra R A] :
    Set.range (BialgHom.mapDomain (A := A) (mkQuotient H (fixedPointHopfIdeal f)).hom) =
      {g : WithConv (H →ₐ[R] A) | ∀ i, BialgHom.mapDomain (A := A) (f i).hom g = g} := by
  ext g
  have hrange : g ∈ Set.range (BialgHom.mapDomain (A := A)
        (mkQuotient H (fixedPointHopfIdeal f)).hom) ↔
      g ∈ quotientPointsSubgroup H (fixedPointHopfIdeal f) (CommAlgCat.of R A) := by
    change (∃ y, BialgHom.mapDomain (A := A) _ y = g) ↔
      ∃ y, quotientPointsHom H (fixedPointHopfIdeal f) (CommAlgCat.of R A) y = g
    refine exists_congr fun y ↦ ?_
    rw [BialgHom.mapDomain_apply, quotientPointsHom_apply]
  rw [hrange, mem_quotientPointsSubgroup_fixedPointHopfIdeal_iff]
  rfl

/-- An automorphism `e : CategoryTheory.Aut H` in `CommHopfAlgCat R` acts on elements by an
`R`-algebra equivalence; because `(x * y).asIso = y.asIso ≪≫ x.asIso`, this is a covariant monoid
homomorphism `CategoryTheory.Aut H →* (H ≃ₐ[R] H)`. -/
private noncomputable def autToAlgEquivHom (H : _root_.CommHopfAlgCat.{v} R) :
    CategoryTheory.Aut H →* (H ≃ₐ[R] H) where
  toFun e := AlgEquiv.ofAlgHom e.asIso.hom.hom.toAlgHom e.asIso.inv.hom.toAlgHom
    (AlgHom.ext fun a ↦ congr($(e.asIso.inv_hom_id).hom a))
    (AlgHom.ext fun a ↦ congr($(e.asIso.hom_inv_id).hom a))
  map_one' := AlgEquiv.ext fun _ ↦ rfl
  map_mul' _ _ := AlgEquiv.ext fun _ ↦ rfl

/-- **Edixhoven's smoothness theorem for commutative Hopf algebras.** If a finite group `Θ` with
`(Nat.card Θ : R)` invertible acts on a smooth commutative Hopf algebra `H` by Hopf-algebra
automorphisms `ρ : Θ →* CategoryTheory.Aut H`, then the fixed-point quotient Hopf algebra is
smooth over `R`. -/
theorem smoothCommHopfAlgProperty_quotient_fixedPointHopfIdeal
    {H : _root_.CommHopfAlgCat.{v} R} (hH : smoothCommHopfAlgProperty R H)
    {Θ : Type w} [Group Θ] [Finite Θ] (ρ : Θ →* CategoryTheory.Aut H)
    (hΘ : IsUnit (Nat.card Θ : R)) :
    smoothCommHopfAlgProperty R
      (quotient H (fixedPointHopfIdeal fun θ ↦ (ρ θ).asIso.hom)) := by
  let _ : Algebra.Smooth R H := (smoothCommHopfAlgProperty_iff H).mp hH
  let actHom : Θ →* (H ≃ₐ[R] H) := (autToAlgEquivHom H).comp ρ
  let _ : MulSemiringAction Θ H := MulSemiringAction.compHom H actHom
  have : SMulCommClass Θ R H := ⟨fun θ r a ↦ map_smul (actHom θ) r a⟩
  have hI : (fixedPointHopfIdeal fun θ ↦ (ρ θ).asIso.hom).toIdeal =
      MulSemiringAction.fixedPointIdeal Θ H :=
    HopfIdeal.fixedPoints_toIdeal_eq_fixedPointIdeal _ fun _ _ ↦ rfl
  let _ : Algebra.Smooth R (H ⧸ MulSemiringAction.fixedPointIdeal Θ H) :=
    MulSemiringAction.smooth_quotient_fixedPointIdeal hΘ
  rw [smoothCommHopfAlgProperty_iff]
  exact Algebra.Smooth.of_equiv (Ideal.quotientEquivAlgOfEq R hI.symm)

end Categorical

section Examples

/-- The factor-swapping endomorphism of `H ⊗[R] H` in `CommHopfAlgCat R`. -/
noncomputable abbrev tensorSwapEnd (H : _root_.CommHopfAlgCat.{v} R) :
    _root_.CommHopfAlgCat.of R (H ⊗[R] H) ⟶ _root_.CommHopfAlgCat.of R (H ⊗[R] H) :=
  _root_.CommHopfAlgCat.ofHom (_root_.Bialgebra.TensorProduct.comm R H H).toBialgHom

/-- The underlying ideal of the swap equalizer Hopf ideal on `H ⊗[R] H` equals the kernel of the
multiplication map `Algebra.TensorProduct.lmul' R`. -/
private theorem equalizerHopfIdeal_tensorSwapEnd_toIdeal (H : _root_.CommHopfAlgCat.{v} R) :
    (equalizerHopfIdeal (tensorSwapEnd H) (𝟙 _)).toIdeal =
      RingHom.ker (Algebra.TensorProduct.lmul' R (S := H)) := by
  rw [← MulSemiringAction.fixedPointIdeal_tensorSwapSubgroup_eq_ker_lmul' R H,
    equalizerHopfIdeal_toIdeal, HopfIdeal.equalizerIdeal_eq_span,
    MulSemiringAction.fixedPointIdeal_zpowers_eq_span]
  rfl

/-- **Diagonal fixed-point subgroup of `G × G`.** For any commutative Hopf algebra `H`, the
quotient of `H ⊗[R] H` by the equalizer Hopf ideal of the swap involution is isomorphic in
`CommHopfAlgCat R` to `H` via coordinate multiplication `_root_.Bialgebra.mulBialgHom R H`. -/
noncomputable def quotientSwapEqualizerIso (H : _root_.CommHopfAlgCat.{v} R) :
    quotient (_root_.CommHopfAlgCat.of R (H ⊗[R] H))
      (equalizerHopfIdeal (tensorSwapEnd H) (𝟙 _)) ≅ H := by
  let mulHom : _root_.CommHopfAlgCat.of R (H ⊗[R] H) ⟶ H :=
    _root_.CommHopfAlgCat.ofHom (_root_.Bialgebra.mulBialgHom R H)
  have hsurj : Function.Surjective mulHom.hom := fun a ↦
    ⟨a ⊗ₜ[R] 1, by simp [mulHom]⟩
  refine quotientIsoOfKerOfSurjectiveEq mulHom hsurj ?_
  have hto : (HopfIdeal.kerOfSurjective mulHom.hom hsurj).toIdeal =
      (equalizerHopfIdeal (tensorSwapEnd H) (𝟙 _)).toIdeal := by
    rw [HopfIdeal.kerOfSurjective_toIdeal, equalizerHopfIdeal_tensorSwapEnd_toIdeal]
    rfl
  exact HopfIdeal.ext fun x ↦ by rw [← HopfIdeal.mem_toIdeal, ← HopfIdeal.mem_toIdeal, hto]

/-- On `A`-points of `𝔾ₘ = Spec R[T;T⁻¹]`, the closed subgroup cut out by the inversion fixed-point
Hopf ideal consists of those units `u = MultiplicativeGroup.pointsMulEquiv g` satisfying
`u ^ 2 = 1`. -/
theorem mem_quotientPointsSubgroup_inversion_iff (A : CommAlgCat.{x} R)
    (g : HopfAlgebra.points (R := R) (H := _root_.CommHopfAlgCat.of R R[T;T⁻¹]) A) :
    g ∈ quotientPointsSubgroup (_root_.CommHopfAlgCat.of R R[T;T⁻¹])
        (HopfIdeal.multiplicativeGroupInversion R) A ↔
      MultiplicativeGroup.pointsMulEquiv g ^ 2 = 1 := by
  have heq : HopfIdeal.multiplicativeGroupInversion R =
      equalizerHopfIdeal
        (_root_.CommHopfAlgCat.ofHom (HopfAlgebra.antipodeBialgHom (R := R) (A := R[T;T⁻¹])))
        (𝟙 (_root_.CommHopfAlgCat.of R R[T;T⁻¹])) := by
    rw [HopfIdeal.multiplicativeGroupInversion_def, equalizerHopfIdeal_def]
    rfl
  rw [heq, mem_quotientPointsSubgroup_equalizerHopfIdeal_iff]
  have hinv : BialgHom.mapDomain (A := A)
      ((_root_.CommHopfAlgCat.ofHom
        (HopfAlgebra.antipodeBialgHom (R := R) (A := R[T;T⁻¹]))).hom) g = g⁻¹ := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro p
    change BialgHom.mapDomain _ g p = g⁻¹ p
    rw [BialgHom.mapDomain_apply_apply, _root_.CommHopfAlgCat.hom_ofHom,
      HopfAlgebra.antipodeBialgHom_apply, WithConv.algHom_inv_apply]
  have hid : BialgHom.mapDomain (A := A)
      (hom (𝟙 (_root_.CommHopfAlgCat.of R R[T;T⁻¹]))) g = g := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro p
    change BialgHom.mapDomain _ g p = g.ofConv p
    rw [BialgHom.mapDomain_apply_apply, _root_.CommHopfAlgCat.id_apply]
  rw [hinv, hid, ← (MultiplicativeGroup.pointsMulEquiv (R := R) (A := A)).injective.eq_iff,
    map_inv, inv_eq_iff_mul_eq_one, ← sq]

end Examples

end CommHopfAlgCat

namespace FiniteTypeCommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- The fixed-point Hopf ideal of a monoid action `ρ : Θ →* CategoryTheory.Aut H` on a finite-type
commutative Hopf algebra `H`. -/
noncomputable def fixedPointHopfIdeal {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H) : HopfIdeal R H :=
  CommHopfAlgCat.fixedPointHopfIdeal fun θ ↦ (ρ θ).asIso.hom.hom

/-- The fixed-point closed subgroup scheme of `ρ : Θ →* CategoryTheory.Aut H`, represented as a
bundled object of `FiniteTypeCommHopfAlgCat R`. -/
noncomputable def fixedPoints {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H) :
    FiniteTypeCommHopfAlgCat.{u, v} R :=
  quotient H (fixedPointHopfIdeal ρ)

/-- The surjective coordinate morphism `H ⟶ fixedPoints ρ` in `FiniteTypeCommHopfAlgCat R`,
representing the closed immersion `(Spec H)^Θ ↪ Spec H`. -/
noncomputable def mkFixedPoints {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H) : H ⟶ fixedPoints ρ :=
  mkQuotient H (fixedPointHopfIdeal ρ)

/-- The coordinate map `H ⟶ fixedPoints ρ` is surjective. -/
theorem mkFixedPoints_surjective {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H) :
    Function.Surjective (toBialgHom (mkFixedPoints ρ)) :=
  CommHopfAlgCat.mkQuotient_surjective H.obj (fixedPointHopfIdeal ρ)

/-- For every commutative `R`-algebra `A`, precomposition with `mkFixedPoints ρ` identifies the
`A`-points of `fixedPoints ρ` with the `A`-points of `H` fixed by every `ρ θ`. -/
theorem range_mapDomain_mkFixedPoints {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H)
    (A : Type x) [CommRing A] [Algebra R A] :
    Set.range (BialgHom.mapDomain (A := A) (toBialgHom (mkFixedPoints ρ))) =
      {g : WithConv (H →ₐ[R] A) |
        ∀ θ : Θ, BialgHom.mapDomain (A := A) (toBialgHom (ρ θ).asIso.hom) g = g} :=
  CommHopfAlgCat.range_mapDomain_mkQuotient_fixedPointHopfIdeal
    (fun θ ↦ (ρ θ).asIso.hom.hom) A

/-- When `ρ = 1` is the trivial action, `fixedPointHopfIdeal ρ` vanishes. -/
@[simp]
theorem fixedPointHopfIdeal_eq_bot_of_eq_one {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] {ρ : Θ →* CategoryTheory.Aut H} (hρ : ρ = 1) :
    fixedPointHopfIdeal ρ = ⊥ := by
  subst hρ
  rw [fixedPointHopfIdeal, CommHopfAlgCat.fixedPointHopfIdeal_eq_bot_iff]
  intro θ
  rfl

/-- When `ρ = 1` is the trivial action, `fixedPoints ρ` is canonically isomorphic to `H` in
`FiniteTypeCommHopfAlgCat R`. -/
noncomputable def fixedPointsIsoOfEqOne {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    {Θ : Type w} [Monoid Θ] {ρ : Θ →* CategoryTheory.Aut H} (hρ : ρ = 1) :
    fixedPoints ρ ≅ H :=
  eqToIso (congrArg (quotient H) (fixedPointHopfIdeal_eq_bot_of_eq_one hρ)) ≪≫
    quotientBotIso H

/-- **Edixhoven's smoothness theorem for finite-type affine group schemes.** Let `H` be a smooth
finite-type commutative Hopf algebra over `R` and let a finite group `Θ` with `(Nat.card Θ : R)`
invertible act on `H` via `ρ : Θ →* CategoryTheory.Aut H`. Then `fixedPoints ρ` is smooth over
`R`. -/
theorem smoothCommHopfAlgProperty_fixedPoints {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    (hH : smoothCommHopfAlgProperty R H.obj) {Θ : Type w} [Group Θ] [Finite Θ]
    (ρ : Θ →* CategoryTheory.Aut H) (hΘ : IsUnit (Nat.card Θ : R)) :
    smoothCommHopfAlgProperty R (fixedPoints ρ).obj := by
  let forgetAut : CategoryTheory.Aut H →* CategoryTheory.Aut H.obj :=
    { toFun e := ⟨(forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
        (_root_.CommHopfAlgCat.{v} R)).mapIso e.asIso⟩
      map_one' := CategoryTheory.Aut.ext rfl
      map_mul' _ _ := CategoryTheory.Aut.ext rfl }
  exact CommHopfAlgCat.smoothCommHopfAlgProperty_quotient_fixedPointHopfIdeal hH
    (forgetAut.comp ρ) hΘ

/-- **Edixhoven's theorem (existential closed-subgroup form, Propositions 3.1 and 3.4).** Fixed
points of a finite group `Θ` of invertible order acting on a smooth affine group scheme of finite
type over `R` are represented by a smooth closed subgroup scheme (`fixedPoints ρ`, via the
surjective coordinate Hopf-algebra morphism `mkFixedPoints ρ`). -/
theorem exists_smooth_fixedPoints {H : FiniteTypeCommHopfAlgCat.{u, v} R}
    (hH : smoothCommHopfAlgProperty R H.obj) (Θ : Type w) [Group Θ] [Finite Θ]
    (ρ : Θ →* CategoryTheory.Aut H) (hΘ : IsUnit (Nat.card Θ : R)) :
    ∃ (H' : FiniteTypeCommHopfAlgCat.{u, v} R) (f : H ⟶ H'),
      smoothCommHopfAlgProperty R H'.obj ∧ Function.Surjective (toBialgHom f) ∧
      ∀ (A : Type x) [CommRing A] [Algebra R A],
        Set.range (BialgHom.mapDomain (A := A) (toBialgHom f)) =
          {g | ∀ θ : Θ,
            BialgHom.mapDomain (A := A) (toBialgHom (ρ θ).asIso.hom) g = g} :=
  ⟨fixedPoints ρ, mkFixedPoints ρ, smoothCommHopfAlgProperty_fixedPoints hH ρ hΘ,
    mkFixedPoints_surjective ρ, range_mapDomain_mkFixedPoints ρ⟩

end FiniteTypeCommHopfAlgCat

end TauCeti
