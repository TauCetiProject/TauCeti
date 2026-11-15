/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import TauCeti.NumberTheory.Padics.AnnularRing.Eval
public import TauCeti.NumberTheory.Padics.AnnularRing.Quotient
import TauCeti.Algebra.MonoidAlgebra.CyclicTwo
import TauCeti.Algebra.MonoidAlgebra.LocalRing
import TauCeti.Algebra.MonoidAlgebra.MvPowerSeries
import TauCeti.Algebra.MonoidAlgebra.PowerSeries
import TauCeti.Algebra.MonoidAlgebra.Quotient

/-!
# Adjoining a finite monoid or the dyadic factor `(ℤ/4ℤ)ˣ` to `ℤ_p⟦T, p/T⟧`

For a finite commutative monoid `M` and `H = AnnularRing p`,
`TauCeti.AnnularRing.mvPowerSeriesQuotientEquiv` identifies `(ℤ_p[M])⟦X_0, X_1⟧ ⧸ (X_0 X_1 - p)`
with `MonoidAlgebra H M`, and `TauCeti.AnnularRing.quotientSpanSingleOneTEquiv` identifies
`H[M] ⧸ (single 1 T)` with `(𝔽_p[M])⟦X⟧`. At `p = 2` for `Δ = (ZMod 4)ˣ`, `H[Δ]` is a local ring
with maximal ideal `(single 1 T, single 1 U, single (-1) 1 - 1)`, no nontrivial idempotents, and an
injective non-surjective joint character evaluation `dyadicToProd` into `H × H`.

## References

* R. Liu, D. Wan and L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J.
  166 (2017), §3.15.
-/

public noncomputable section

open PowerSeries

namespace TauCeti.AnnularRing

section FiniteMonoid
variable {p : ℕ} [Fact p.Prime]

section CommMonoid
variable (M : Type*) [CommMonoid M]

theorem span_p_single_one_T_eq_span_single_one_T :
    Ideal.span {(p : MonoidAlgebra (AnnularRing p) M),
      MonoidAlgebra.single 1 (T : AnnularRing p)} =
      Ideal.span {MonoidAlgebra.single 1 (T : AnnularRing p)} := by
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_mono (by simp))
  rintro x (rfl | rfl)
  · refine Ideal.mem_span_singleton'.2 ⟨MonoidAlgebra.single 1 U, ?_⟩
    rw [MonoidAlgebra.single_mul_single, one_mul, U_mul_T]
    exact (map_natCast MonoidAlgebra.singleOneRingHom p).symm
  · exact Ideal.subset_span rfl

theorem span_single_one_T_eq_map :
    Ideal.span {MonoidAlgebra.single (1 : M) (T : AnnularRing p)} =
      Ideal.map (MonoidAlgebra.singleOneRingHom :
        AnnularRing p →+* MonoidAlgebra (AnnularRing p) M)
        (Ideal.span {(T : AnnularRing p)}) := by
  rw [Ideal.map_span, Set.image_singleton]; rfl

end CommMonoid

section Finite
variable (M : Type*) [CommMonoid M] [Finite M]

private theorem map_span_rel_mvPowerSeriesAlgEquiv_symm :
    Ideal.map (MonoidAlgebra.singleOneRingHom :
        MvPowerSeries (Fin 2) ℤ_[p] →+* MonoidAlgebra (MvPowerSeries (Fin 2) ℤ_[p]) M)
      (Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C (p : ℤ_[p])}) =
    Ideal.map ((MonoidAlgebra.mvPowerSeriesAlgEquiv ℤ_[p] (Fin 2) ℤ_[p] M).symm :
        MvPowerSeries (Fin 2) (MonoidAlgebra ℤ_[p] M) →+*
          MonoidAlgebra (MvPowerSeries (Fin 2) ℤ_[p]) M)
      (Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1 -
        MvPowerSeries.C (p : MonoidAlgebra ℤ_[p] M)}) := by
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]; congr 2
  have hp : (p : MonoidAlgebra ℤ_[p] M) = MonoidAlgebra.single 1 (p : ℤ_[p]) := by
    rw [← map_natCast (MonoidAlgebra.singleOneRingHom (R := ℤ_[p]) (M := M))]; rfl
  simp [MonoidAlgebra.singleOneRingHom, hp, MonoidAlgebra.single_sub]

/-- Halo comparison `(ℤ_p[M])⟦X_0, X_1⟧ ⧸ (X_0 X_1 - p) ≃ₐ[ℤ_p] MonoidAlgebra (AnnularRing p) M`. -/
def mvPowerSeriesQuotientEquiv :
    (MvPowerSeries (Fin 2) (MonoidAlgebra ℤ_[p] M) ⧸
      Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1 -
        MvPowerSeries.C (p : MonoidAlgebra ℤ_[p] M)}) ≃ₐ[ℤ_[p]]
      MonoidAlgebra (AnnularRing p) M :=
  (Ideal.quotientEquivAlg _ _
    (MonoidAlgebra.mvPowerSeriesAlgEquiv ℤ_[p] (Fin 2) ℤ_[p] M).symm
    (map_span_rel_mvPowerSeriesAlgEquiv_symm M)).trans <|
    (MonoidAlgebra.quotientAlgEquiv ℤ_[p] M _).trans
      (MonoidAlgebra.mapAlgEquiv ℤ_[p] M (quotientMvPowerSeriesEquiv (p := p)))

@[simp] theorem mvPowerSeriesQuotientEquiv_mk_X_zero :
    mvPowerSeriesQuotientEquiv M (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) =
      MonoidAlgebra.single 1 (T : AnnularRing p) := by
  simp [mvPowerSeriesQuotientEquiv, MonoidAlgebra.mapAlgEquiv]
@[simp] theorem mvPowerSeriesQuotientEquiv_mk_X_one :
    mvPowerSeriesQuotientEquiv M (Ideal.Quotient.mk _ (MvPowerSeries.X 1)) =
      MonoidAlgebra.single 1 (U : AnnularRing p) := by
  simp [mvPowerSeriesQuotientEquiv, MonoidAlgebra.mapAlgEquiv]
@[simp] theorem mvPowerSeriesQuotientEquiv_mk_C_single (m : M) (c : ℤ_[p]) :
    mvPowerSeriesQuotientEquiv M
        (Ideal.Quotient.mk _ (MvPowerSeries.C (MonoidAlgebra.single m c))) =
      MonoidAlgebra.single m (algebraMap ℤ_[p] (AnnularRing p) c) := by
  simp [mvPowerSeriesQuotientEquiv, MonoidAlgebra.mapAlgEquiv, evalTU_C]

/-- Boundary quotient `H[M] ⧸ (single 1 T) ≃+* (𝔽_p[M])⟦X⟧`, sending `single 1 U` to `X`. -/
def quotientSpanSingleOneTEquiv :
    (MonoidAlgebra (AnnularRing p) M ⧸
      Ideal.span {MonoidAlgebra.single (1 : M) (T : AnnularRing p)}) ≃+*
      (MonoidAlgebra (ZMod p) M)⟦X⟧ :=
  (Ideal.quotEquivOfEq (span_single_one_T_eq_map M)).trans <|
    (MonoidAlgebra.quotientAlgEquiv ℤ M (Ideal.span {(T : AnnularRing p)})).toRingEquiv.trans <|
      (MonoidAlgebra.mapRingEquiv M (quotientSpanTEquiv (p := p))).trans
        (MonoidAlgebra.powerSeriesAlgEquiv (ZMod p) (ZMod p) M).toRingEquiv

@[simp] theorem quotientSpanSingleOneTEquiv_mk_single_one_U :
    quotientSpanSingleOneTEquiv M
        (Ideal.Quotient.mk _ (MonoidAlgebra.single 1 (U : AnnularRing p))) = PowerSeries.X := by
  simp [quotientSpanSingleOneTEquiv]

@[simp] theorem quotientSpanSingleOneTEquiv_mk_single_algebraMap (m : M) (c : ℤ_[p]) :
    quotientSpanSingleOneTEquiv M
        (Ideal.Quotient.mk _ (MonoidAlgebra.single m (algebraMap ℤ_[p] (AnnularRing p) c))) =
      PowerSeries.C (MonoidAlgebra.single m (PadicInt.toZMod c)) := by
  have hq :
      quotientSpanTEquiv (algebraMap ℤ_[p] (AnnularRing p ⧸ Ideal.span {(T : AnnularRing p)}) c) =
        PowerSeries.C (PadicInt.toZMod c) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] (AnnularRing p), Ideal.Quotient.algebraMap_eq,
      quotientSpanTEquiv_mk]
    ext n; rcases eq_or_ne n 0 with rfl | hn
    · simp [coeff_algebraMap]
    · have hu : uCoeff (algebraMap ℤ_[p] (AnnularRing p) c) n = 0 :=
        mul_left_cancel₀ (pow_ne_zero n (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)) <| by
          rw [pow_mul_uCoeff, coeff_algebraMap, ite_eq_right (by omega), mul_zero]
      simp [PowerSeries.coeff_C, hn, hu]
  simp [quotientSpanSingleOneTEquiv, hq]

end Finite
end FiniteMonoid

/-! ### The dyadic finite factor `Δ = (ZMod 4)ˣ` at `p = 2` -/

section Dyadic

/-- Multiplicative isomorphism `(ZMod 4)ˣ ≃* Multiplicative (ZMod 2)` (`1 ↦ 1`, `-1 ↦ ofAdd 1`). -/
def unitsZModFourMulEquiv : (ZMod 4)ˣ ≃* Multiplicative (ZMod 2) where
  toFun u := if u = 1 then 1 else Multiplicative.ofAdd 1
  invFun g := if g = 1 then 1 else -1
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

theorem unitsZModFourMulEquiv_one : unitsZModFourMulEquiv 1 = 1 := (rfl)
@[simp] theorem unitsZModFourMulEquiv_neg_one :
    unitsZModFourMulEquiv (-1 : (ZMod 4)ˣ) = Multiplicative.ofAdd 1 := by decide
@[simp] theorem unitsZModFourMulEquiv_symm_ofAdd_one :
    unitsZModFourMulEquiv.symm (Multiplicative.ofAdd 1) = -1 := by decide

private theorem unitsZModFour_eq_one_or_neg_one : ∀ u : (ZMod 4)ˣ, u = 1 ∨ u = -1 := by decide
private theorem neg_one_ne_one_unitsZModFour : (-1 : (ZMod 4)ˣ) ≠ 1 := by decide
private theorem isPGroup_unitsZModFour : IsPGroup 2 (ZMod 4)ˣ :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_eq_fintype_card]; decide)

instance instIsLocalRingDyadicGroupRing :
    IsLocalRing (MonoidAlgebra (AnnularRing 2) (ZMod 4)ˣ) :=
  TauCeti.MonoidAlgebra.isLocalRing_of_isPGroup (not_isUnit_p (p := 2)) isPGroup_unitsZModFour

theorem eq_single_one_add_single_neg_one {R : Type*} [Semiring R]
    (x : MonoidAlgebra R (ZMod 4)ˣ) :
    x = MonoidAlgebra.single 1 (x.coeff 1) + MonoidAlgebra.single (-1) (x.coeff (-1)) := by
  ext u; rcases unitsZModFour_eq_one_or_neg_one u with rfl | rfl <;>
    simp [MonoidAlgebra.coeff_single, neg_one_ne_one_unitsZModFour,
      neg_one_ne_one_unitsZModFour.symm]

/-- Residue homomorphism `MonoidAlgebra (AnnularRing 2) (ZMod 4)ˣ →+* ZMod 2`. -/
def dyadicGroupRingResidue : MonoidAlgebra (AnnularRing 2) (ZMod 4)ˣ →+* ZMod 2 :=
  (residueTU (p := 2)).comp
    (MonoidAlgebra.lift (AnnularRing 2) (AnnularRing 2) (ZMod 4)ˣ 1).toRingHom

@[simp] theorem dyadicGroupRingResidue_single (u : (ZMod 4)ˣ) (x : AnnularRing 2) :
    dyadicGroupRingResidue (MonoidAlgebra.single u x) = residueTU x := by
  simp [dyadicGroupRingResidue]

theorem ker_dyadicGroupRingResidue :
    RingHom.ker dyadicGroupRingResidue =
      IsLocalRing.maximalIdeal (MonoidAlgebra (AnnularRing 2) (ZMod 4)ˣ) :=
  IsLocalRing.eq_maximalIdeal
    (RingHom.ker_isMaximal_of_surjective dyadicGroupRingResidue
      (ZMod.ringHom_surjective dyadicGroupRingResidue))

/-- The maximal ideal of `MonoidAlgebra (AnnularRing 2) (ZMod 4)ˣ` is
`(single 1 T, single 1 U, single (-1) 1 - 1)`. -/
theorem maximalIdeal_dyadicGroupRing_eq_span :
    IsLocalRing.maximalIdeal (MonoidAlgebra (AnnularRing 2) (ZMod 4)ˣ) =
      Ideal.span {MonoidAlgebra.single 1 (T : AnnularRing 2),
        MonoidAlgebra.single 1 (U : AnnularRing 2),
        MonoidAlgebra.single (-1 : (ZMod 4)ˣ) (1 : AnnularRing 2) - 1} := by
  rw [← ker_dyadicGroupRingResidue]
  refine le_antisymm (fun x hx ↦ ?_) (Ideal.span_le.2 ?_)
  · rw [RingHom.mem_ker] at hx
    have hx_split : x = MonoidAlgebra.single 1 (x.coeff 1 + x.coeff (-1)) +
        MonoidAlgebra.single 1 (x.coeff (-1)) * (MonoidAlgebra.single (-1 : (ZMod 4)ˣ) 1 - 1) := by
      conv_lhs => rw [eq_single_one_add_single_neg_one x]
      rw [mul_sub, MonoidAlgebra.single_mul_single, one_mul, mul_one, mul_one,
        MonoidAlgebra.single_add]; abel
    have hval := congr_arg dyadicGroupRingResidue (eq_single_one_add_single_neg_one x)
    rw [hx, map_add, dyadicGroupRingResidue_single, dyadicGroupRingResidue_single,
      ← map_add] at hval
    have hmem_TU : x.coeff 1 + x.coeff (-1) ∈ Ideal.span {(T : AnnularRing 2), U} := by
      rw [← maximalIdeal_eq_span_T_U, ← ker_residueTU, RingHom.mem_ker]; exact hval.symm
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hmem_TU
    have hmul (r s : AnnularRing 2) :
        MonoidAlgebra.single (1 : (ZMod 4)ˣ) (r * s) =
          MonoidAlgebra.single 1 r * MonoidAlgebra.single 1 s := by simp
    rw [hx_split, ← hab, MonoidAlgebra.single_add, hmul, hmul]
    exact Ideal.add_mem _
      (Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  · rintro y (rfl | rfl | rfl) <;> simp [RingHom.mem_ker]

theorem single_neg_one_sub_one_notMem_map_maximalIdeal :
    MonoidAlgebra.single (-1 : (ZMod 4)ˣ) (1 : AnnularRing 2) - 1 ∉
      Ideal.map (MonoidAlgebra.singleOneRingHom :
        AnnularRing 2 →+* MonoidAlgebra (AnnularRing 2) (ZMod 4)ˣ)
        (IsLocalRing.maximalIdeal (AnnularRing 2)) := by
  rw [MonoidAlgebra.mem_map_singleOneRingHom_iff]; intro h; have h1 := h (-1)
  rw [MonoidAlgebra.one_def, MonoidAlgebra.coeff_sub, Finsupp.coe_sub, Pi.sub_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_eq_same, MonoidAlgebra.coeff_single,
    Finsupp.single_eq_of_ne neg_one_ne_one_unitsZModFour, sub_zero,
    IsLocalRing.mem_maximalIdeal] at h1
  exact h1 isUnit_one

@[simp] theorem isIdempotentElem_dyadicGroupRing_iff
    {e : MonoidAlgebra (AnnularRing 2) (ZMod 4)ˣ} : IsIdempotentElem e ↔ e = 0 ∨ e = 1 := by
  let φ := MonoidAlgebra.domCongr (AnnularRing 2) (AnnularRing 2) unitsZModFourMulEquiv
  have hφ : IsIdempotentElem (φ e) ↔ IsIdempotentElem e := by
    simp [IsIdempotentElem, ← map_mul, φ.injective.eq_iff]
  rw [← hφ, MonoidAlgebra.isIdempotentElem_cyclicTwo_iff (AnnularRing 2) (not_isUnit_p (p := 2)),
    ← map_zero φ, ← map_one φ, φ.injective.eq_iff, φ.injective.eq_iff]

/-- Joint evaluation of `MonoidAlgebra (AnnularRing 2) (ZMod 4)ˣ` at both characters of `(ZMod 4)ˣ`.
-/
def dyadicToProd :
    MonoidAlgebra (AnnularRing 2) (ZMod 4)ˣ →ₐ[AnnularRing 2] AnnularRing 2 × AnnularRing 2 :=
  (MonoidAlgebra.cyclicTwoToProd (AnnularRing 2)).comp
    (MonoidAlgebra.domCongr (AnnularRing 2) (AnnularRing 2) unitsZModFourMulEquiv).toAlgHom

@[simp] theorem dyadicToProd_single_one (a : AnnularRing 2) :
    dyadicToProd (MonoidAlgebra.single 1 a) = (a, a) := by
  simp [dyadicToProd, MonoidAlgebra.domCongr_toAlgHom]
@[simp] theorem dyadicToProd_single_neg_one (b : AnnularRing 2) :
    dyadicToProd (MonoidAlgebra.single (-1) b) = (b, -b) := by
  simp [dyadicToProd, MonoidAlgebra.domCongr_toAlgHom]

theorem dyadicToProd_apply (x : MonoidAlgebra (AnnularRing 2) (ZMod 4)ˣ) :
    dyadicToProd x = (x.coeff 1 + x.coeff (-1), x.coeff 1 - x.coeff (-1)) := by
  conv_lhs => rw [eq_single_one_add_single_neg_one x]
  simp [map_add, sub_eq_add_neg]

theorem dyadicToProd_injective : Function.Injective dyadicToProd :=
  (injective_iff_map_eq_zero _).2 fun x hx ↦ by
    rw [dyadicToProd_apply, Prod.mk_eq_zero] at hx
    have ha : x.coeff 1 = 0 :=
      (mul_eq_zero.1 (by linear_combination hx.1 + hx.2 : (2 : AnnularRing 2) * x.coeff 1 = 0))
        |>.resolve_left two_ne_zero
    have hb : x.coeff (-1) = 0 := by linear_combination hx.1 - ha
    rw [eq_single_one_add_single_neg_one x, ha, hb, MonoidAlgebra.single_zero,
      MonoidAlgebra.single_zero, add_zero]

theorem one_zero_notMem_range_dyadicToProd :
    ((1 : AnnularRing 2), (0 : AnnularRing 2)) ∉ Set.range dyadicToProd := by
  rintro ⟨x, hx⟩; rw [dyadicToProd_apply, Prod.mk.injEq] at hx
  exact not_isUnit_p (p := 2) (IsUnit.of_mul_eq_one (x.coeff 1) (by linear_combination hx.1 + hx.2))

theorem not_surjective_dyadicToProd : ¬ Function.Surjective dyadicToProd :=
  fun h ↦ one_zero_notMem_range_dyadicToProd (h (1, 0))

end Dyadic
end TauCeti.AnnularRing
