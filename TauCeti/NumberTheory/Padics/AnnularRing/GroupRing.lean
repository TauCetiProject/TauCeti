/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import TauCeti.NumberTheory.Padics.AnnularRing.Quotient
import TauCeti.Algebra.MonoidAlgebra.Augmentation
import TauCeti.Algebra.MonoidAlgebra.CyclicTwo
import TauCeti.Algebra.MonoidAlgebra.LocalRing
import TauCeti.Algebra.MonoidAlgebra.MvPowerSeries
import TauCeti.Algebra.MonoidAlgebra.Quotient
import TauCeti.Data.ZMod.Four
import TauCeti.NumberTheory.Padics.AnnularRing.Eval

/-!
# Adjoining a finite monoid or the dyadic factor `(ℤ/4ℤ)ˣ` to `ℤ_p⟦T, p/T⟧`

For a finite commutative monoid `M` and `H = AnnularRing p`,
`TauCeti.AnnularRing.quotientMvPowerSeriesMonoidAlgebraEquiv` identifies
`(ℤ_p[M])⟦X_0, X_1⟧ ⧸ (X_0 X_1 - p)` with `MonoidAlgebra H M`, and
`TauCeti.AnnularRing.quotientSpanSingleOneTEquiv` identifies `H[M] ⧸ (single 1 T)` with
`(𝔽_p[M])⟦X⟧`. At `p = 2` for `Δ = (ZMod 4)ˣ`, `H[Δ]` is a local ring
(`instIsLocalRingDyadicGroupRing`, hence has no nontrivial idempotents via
`IsIdempotentElem.eq_zero_or_eq_one_of_isLocalRing`) with maximal ideal
`(single 1 T, single 1 U, single (-1) 1 - 1)` and an injective non-surjective joint character
evaluation `dyadicToProd` into `H × H`.

## References

* R. Liu, D. Wan and L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J.
  166 (2017), §3.15.
-/

public noncomputable section

open PowerSeries

namespace TauCeti.AnnularRing

section FiniteMonoid
variable {p : ℕ} [Fact p.Prime]

section Monoid
variable (M : Type*) [Monoid M]

/-- In `(AnnularRing p)[M]`, `(p, single 1 T)` collapses to `(single 1 T)` since `p = U T`. -/
theorem span_p_single_one_T_eq_span_single_one_T :
    Ideal.span {(p : MonoidAlgebra (AnnularRing p) M),
      MonoidAlgebra.single 1 (T : AnnularRing p)} =
      Ideal.span {MonoidAlgebra.single 1 (T : AnnularRing p)} := by
  simpa [Ideal.map_span, Set.image_pair, Set.image_singleton, MonoidAlgebra.singleOneRingHom,
    ← MonoidAlgebra.natCast_def] using congrArg (Ideal.map (MonoidAlgebra.singleOneRingHom :
      AnnularRing p →+* MonoidAlgebra (AnnularRing p) M)) (span_p_T_eq_span_T (p := p))

/-- `(single 1 T)` in `(AnnularRing p)[M]` is the extension of `(T)` along `singleOneRingHom`. -/
theorem span_single_one_T_eq_map :
    Ideal.span {MonoidAlgebra.single (1 : M) (T : AnnularRing p)} =
      Ideal.map (MonoidAlgebra.singleOneRingHom : AnnularRing p →+* MonoidAlgebra (AnnularRing p) M)
        (Ideal.span {(T : AnnularRing p)}) := by
  simp [Ideal.map_span, MonoidAlgebra.singleOneRingHom]
end Monoid

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
  simp [MonoidAlgebra.singleOneRingHom, MonoidAlgebra.natCast_def, MonoidAlgebra.single_sub]

/-- Halo comparison `(ℤ_p[M])⟦X_0, X_1⟧ ⧸ (X_0 X_1 - p) ≃ₐ[ℤ_p] MonoidAlgebra (AnnularRing p) M`. -/
def quotientMvPowerSeriesMonoidAlgebraEquiv :
    (MvPowerSeries (Fin 2) (MonoidAlgebra ℤ_[p] M) ⧸
      Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1 -
        MvPowerSeries.C (p : MonoidAlgebra ℤ_[p] M)}) ≃ₐ[ℤ_[p]]
      MonoidAlgebra (AnnularRing p) M :=
  (Ideal.quotientEquivAlg _ _ (MonoidAlgebra.mvPowerSeriesAlgEquiv ℤ_[p] (Fin 2) ℤ_[p] M).symm
    (map_span_rel_mvPowerSeriesAlgEquiv_symm M)).trans <|
    (MonoidAlgebra.quotientAlgEquiv ℤ_[p] M _).trans
      (MonoidAlgebra.mapAlgEquiv ℤ_[p] M (quotientMvPowerSeriesEquiv (p := p)))

@[simp] theorem quotientMvPowerSeriesMonoidAlgebraEquiv_mk_X_zero :
    quotientMvPowerSeriesMonoidAlgebraEquiv M (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) =
      MonoidAlgebra.single 1 (T : AnnularRing p) := by
  simp [quotientMvPowerSeriesMonoidAlgebraEquiv, MonoidAlgebra.mapAlgEquiv]
@[simp] theorem quotientMvPowerSeriesMonoidAlgebraEquiv_mk_X_one :
    quotientMvPowerSeriesMonoidAlgebraEquiv M (Ideal.Quotient.mk _ (MvPowerSeries.X 1)) =
      MonoidAlgebra.single 1 (U : AnnularRing p) := by
  simp [quotientMvPowerSeriesMonoidAlgebraEquiv, MonoidAlgebra.mapAlgEquiv]
@[simp] theorem quotientMvPowerSeriesMonoidAlgebraEquiv_mk_C_single (m : M) (c : ℤ_[p]) :
    quotientMvPowerSeriesMonoidAlgebraEquiv M
        (Ideal.Quotient.mk _ (MvPowerSeries.C (MonoidAlgebra.single m c))) =
      MonoidAlgebra.single m (algebraMap ℤ_[p] (AnnularRing p) c) := by
  simp [quotientMvPowerSeriesMonoidAlgebraEquiv, MonoidAlgebra.mapAlgEquiv, evalTU_C]

/-- Boundary quotient `H[M] ⧸ (single 1 T) ≃+* (𝔽_p[M])⟦X⟧`, sending `single 1 U` to `X`. -/
def quotientSpanSingleOneTEquiv :
    (MonoidAlgebra (AnnularRing p) M ⧸
      Ideal.span {MonoidAlgebra.single (1 : M) (T : AnnularRing p)}) ≃+*
      (MonoidAlgebra (ZMod p) M)⟦X⟧ :=
  (Ideal.quotEquivOfEq (span_single_one_T_eq_map M)).trans <|
    (MonoidAlgebra.quotientAlgEquiv ℤ M (Ideal.span {(T : AnnularRing p)})).toRingEquiv.trans <|
      (MonoidAlgebra.mapRingEquiv M (quotientSpanTEquiv (p := p))).trans
        (MonoidAlgebra.mvPowerSeriesAlgEquiv (ZMod p) Unit (ZMod p) M).toRingEquiv

@[simp] theorem quotientSpanSingleOneTEquiv_mk_single_one_U :
    quotientSpanSingleOneTEquiv M
        (Ideal.Quotient.mk _ (MonoidAlgebra.single 1 (U : AnnularRing p))) = PowerSeries.X := by
  simp [quotientSpanSingleOneTEquiv, PowerSeries.X_apply]
@[simp] theorem quotientSpanSingleOneTEquiv_mk_single_algebraMap (m : M) (c : ℤ_[p]) :
    quotientSpanSingleOneTEquiv M
        (Ideal.Quotient.mk _ (MonoidAlgebra.single m (algebraMap ℤ_[p] (AnnularRing p) c))) =
      PowerSeries.C (MonoidAlgebra.single m (PadicInt.toZMod c)) := by
  have hq : quotientSpanTEquiv
      (algebraMap ℤ_[p] (AnnularRing p ⧸ Ideal.span {(T : AnnularRing p)}) c) =
      PowerSeries.C (PadicInt.toZMod c) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] (AnnularRing p), Ideal.Quotient.algebraMap_eq,
      quotientSpanTEquiv_mk, modT_algebraMap]
  simp [quotientSpanSingleOneTEquiv, hq, PowerSeries.C_apply]
end Finite
end FiniteMonoid

/-! ### The dyadic finite factor `Δ = (ZMod 4)ˣ` at `p = 2` -/

section Dyadic

instance instIsLocalRingDyadicGroupRing :
    IsLocalRing (MonoidAlgebra (AnnularRing 2) (ZMod 4)ˣ) :=
  TauCeti.MonoidAlgebra.isLocalRing_of_isPGroup (not_isUnit_p (p := 2)) ZMod.isPGroup_unitsFour

/-- Residue homomorphism `MonoidAlgebra (AnnularRing 2) (ZMod 4)ˣ →+* ZMod 2`. -/
def dyadicGroupRingResidue : MonoidAlgebra (AnnularRing 2) (ZMod 4)ˣ →+* ZMod 2 :=
  (residueTU (p := 2)).comp (MonoidAlgebra.augmentation (AnnularRing 2) (ZMod 4)ˣ)
@[simp] theorem dyadicGroupRingResidue_single (u : (ZMod 4)ˣ) (x : AnnularRing 2) :
    dyadicGroupRingResidue (MonoidAlgebra.single u x) = residueTU x := by
  simp [dyadicGroupRingResidue]

/-- The kernel of `dyadicGroupRingResidue` is the unique maximal ideal of the local ring
`MonoidAlgebra (AnnularRing 2) (ZMod 4)ˣ`. -/
theorem ker_dyadicGroupRingResidue :
    RingHom.ker dyadicGroupRingResidue =
      IsLocalRing.maximalIdeal (MonoidAlgebra (AnnularRing 2) (ZMod 4)ˣ) :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective dyadicGroupRingResidue
    (ZMod.ringHom_surjective dyadicGroupRingResidue))

/-- The maximal ideal of `MonoidAlgebra (AnnularRing 2) (ZMod 4)ˣ` is
`(single 1 T, single 1 U, single (-1) 1 - 1)`. -/
theorem maximalIdeal_dyadicGroupRing_eq_span :
    IsLocalRing.maximalIdeal (MonoidAlgebra (AnnularRing 2) (ZMod 4)ˣ) =
      Ideal.span {MonoidAlgebra.single 1 (T : AnnularRing 2),
        MonoidAlgebra.single 1 (U : AnnularRing 2),
        MonoidAlgebra.single (-1 : (ZMod 4)ˣ) (1 : AnnularRing 2) - 1} := by
  rw [← ker_dyadicGroupRingResidue]
  refine le_antisymm (fun x hx ↦ ?_) (Ideal.span_le.2 fun y hy ↦ by
    rcases hy with rfl | rfl | rfl <;> simp [RingHom.mem_ker])
  rw [RingHom.mem_ker] at hx
  have hx_split : x = MonoidAlgebra.single 1 (x.coeff 1 + x.coeff (-1)) +
      MonoidAlgebra.single 1 (x.coeff (-1)) * (MonoidAlgebra.single (-1 : (ZMod 4)ˣ) 1 - 1) := by
    conv_lhs => rw [x.eq_single_one_add_single_neg_one]
    rw [mul_sub, MonoidAlgebra.single_mul_single, one_mul, mul_one, mul_one,
      MonoidAlgebra.single_add]; abel
  have hval : residueTU (x.coeff 1 + x.coeff (-1)) = 0 := by
    simpa [hx] using (congr_arg dyadicGroupRingResidue x.eq_single_one_add_single_neg_one).symm
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 (by
    rwa [← maximalIdeal_eq_span_T_U, ← ker_residueTU, RingHom.mem_ker] :
      x.coeff 1 + x.coeff (-1) ∈ Ideal.span {(T : AnnularRing 2), U})
  have hmul (r s : AnnularRing 2) : MonoidAlgebra.single (1 : (ZMod 4)ˣ) (r * s) =
      MonoidAlgebra.single 1 r * MonoidAlgebra.single 1 s := by simp
  rw [hx_split, ← hab, MonoidAlgebra.single_add, hmul, hmul]
  exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

/-- The augmentation generator `single (-1) 1 - 1` lies outside the extended maximal ideal of
`AnnularRing 2`, showing the maximal ideal strictly enlarges the extension of `(T, U)`. -/
theorem single_neg_one_sub_one_notMem_map_maximalIdeal :
    MonoidAlgebra.single (-1 : (ZMod 4)ˣ) (1 : AnnularRing 2) - 1 ∉
      Ideal.map (MonoidAlgebra.singleOneRingHom :
        AnnularRing 2 →+* MonoidAlgebra (AnnularRing 2) (ZMod 4)ˣ)
        (IsLocalRing.maximalIdeal (AnnularRing 2)) := by
  rw [MonoidAlgebra.mem_map_singleOneRingHom_iff]; intro h
  have h1 : (MonoidAlgebra.single (-1 : (ZMod 4)ˣ) (1 : AnnularRing 2) - 1).coeff (-1) = 1 := by
    simp [MonoidAlgebra.one_def, ZMod.neg_one_ne_one_unitsFour]
  exact (IsLocalRing.mem_maximalIdeal _).1 (h1 ▸ h (-1)) isUnit_one

/-- Joint evaluation of `MonoidAlgebra (AnnularRing 2) (ZMod 4)ˣ` at both characters of
`(ZMod 4)ˣ`. -/
def dyadicToProd :
    MonoidAlgebra (AnnularRing 2) (ZMod 4)ˣ →ₐ[AnnularRing 2] AnnularRing 2 × AnnularRing 2 :=
  (MonoidAlgebra.cyclicTwoToProd (AnnularRing 2)).comp
    (MonoidAlgebra.domCongr (AnnularRing 2) (AnnularRing 2) ZMod.unitsFourMulEquiv).toAlgHom
@[simp] theorem dyadicToProd_single_one (a : AnnularRing 2) :
    dyadicToProd (MonoidAlgebra.single 1 a) = (a, a) := by
  simp [dyadicToProd, MonoidAlgebra.domCongr_toAlgHom]
@[simp] theorem dyadicToProd_single_neg_one (b : AnnularRing 2) :
    dyadicToProd (MonoidAlgebra.single (-1) b) = (b, -b) := by
  simp [dyadicToProd, MonoidAlgebra.domCongr_toAlgHom]

/-- Explicit formula for joint character evaluation: `a · 1 + b · (-1) ↦ (a + b, a - b)`. -/
theorem dyadicToProd_apply (x : MonoidAlgebra (AnnularRing 2) (ZMod 4)ˣ) :
    dyadicToProd x = (x.coeff 1 + x.coeff (-1), x.coeff 1 - x.coeff (-1)) := by
  conv_lhs => rw [x.eq_single_one_add_single_neg_one]
  simp [map_add, sub_eq_add_neg]

/-- Joint character evaluation `dyadicToProd` is injective, as `2` is a non-zero-divisor. -/
theorem dyadicToProd_injective : Function.Injective dyadicToProd :=
  (injective_iff_map_eq_zero _).2 fun x hx ↦ by
    rw [dyadicToProd_apply, Prod.mk_eq_zero] at hx
    have ha : x.coeff 1 = 0 := (mul_eq_zero.1 (by linear_combination hx.1 + hx.2 :
      (2 : AnnularRing 2) * x.coeff 1 = 0)).resolve_left two_ne_zero
    have hb : x.coeff (-1) = 0 := by linear_combination hx.1 - ha
    simpa [ha, hb] using x.eq_single_one_add_single_neg_one

/-- `(1, 0) ∈ AnnularRing 2 × AnnularRing 2` is not in the range of `dyadicToProd`, because `2` is
not a unit in `AnnularRing 2`. -/
theorem one_zero_notMem_range_dyadicToProd :
    ((1 : AnnularRing 2), (0 : AnnularRing 2)) ∉ Set.range dyadicToProd := by
  rintro ⟨x, hx⟩; rw [dyadicToProd_apply, Prod.mk.injEq] at hx
  exact not_isUnit_p (p := 2) (IsUnit.of_mul_eq_one (x.coeff 1) (by linear_combination hx.1 + hx.2))

/-- `dyadicToProd` is not surjective, so the dyadic group ring does not split integrally into two
copies of `AnnularRing 2`. -/
theorem not_surjective_dyadicToProd : ¬ Function.Surjective dyadicToProd :=
  fun h ↦ one_zero_notMem_range_dyadicToProd (h (1, 0))

end Dyadic
end TauCeti.AnnularRing
