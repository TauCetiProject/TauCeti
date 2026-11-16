/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.MapsInfinity
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Neg
public import TauCeti.RingTheory.FormalGroup.ZSMul
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Hom
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Torsion.Free
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Comp
import TauCeti.AlgebraicGeometry.EllipticCurve.Weierstrass
import TauCeti.RingTheory.PowerSeries.Evaluation
import TauCeti.RingTheory.PowerSeries.PiTopology
import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic

/-!
# Formal power series of negation and multiplication-by-`n` isogenies

For a Weierstrass curve `W` over a field `K`, the formal power series induced by the negation
isogeny is the formal group's inverse series (`TauCeti.Isogeny.formalSeries_negIsogeny`). When `W`
is elliptic, the formal power series induced by every multiplication-by-`n` isogeny `[n]` agrees
with the formal group's integer multiplication series `[n](X)`
(`TauCeti.Isogeny.formalSeries_mulByIntIsogeny`).

This bridges global invariants of the multiplication-by-`p` isogeny `[p]` — in particular its
inseparable degree, which equals the order of its formal series by
`TauCeti.Isogeny.order_formalSeries_eq_inseparableDegree` — to `(formalGroup W).zsmulSeries p` and
hence to the height of the formal group of `W` in
`TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Classification`.

## Main results

* `TauCeti.Isogeny.formalSeries_negIsogeny`: the formal series of `negIsogeny` is the formal group's
  inverse series.
* `TauCeti.Isogeny.formalSeries_mulByIntIsogeny`: the formal series of `[n]` is
  `(formalGroup W).zsmulSeries n`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4.
-/

public section

open WeierstrassCurve HahnSeries
open scoped LaurentSeries PowerSeries Topology

namespace TauCeti.Isogeny

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

/-- **The formal series of the negation isogeny is the formal-group inverse series.** This holds
for every Weierstrass curve over a field, without a nonsingularity hypothesis. -/
@[simp]
theorem formalSeries_negIsogeny :
    (negIsogeny W.toAffine).formalSeries = (formalGroup W).addInvX := by
  rw [W.formalGroup_addInvX, formalSeries_eq_iff]
  set φ := W.functionFieldLaurentExpansion
  set x : K⸨X⸩ := φ W.toAffine.genericX
  set y : K⸨X⸩ := φ W.toAffine.genericY
  have hy : y ≠ 0 := (map_ne_zero_iff φ φ.injective).mpr W.toAffine.genericY_ne_zero
  have hX : ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) = -x / y := by
    rw [← W.functionFieldLaurentExpansion_neg_genericX_div_genericY, map_div₀, map_neg]
  have hW : ((W.formalW : K⟦X⟧) : K⸨X⸩) = -y⁻¹ := by
    rw [← W.functionFieldLaurentExpansion_neg_inv_genericY, map_neg, map_inv₀]
  have hd_mul :
      ((W.formalInverseDenom : K⟦X⟧) : K⸨X⸩) *
        ((PowerSeries.invOfUnit W.formalInverseDenom 1 : K⟦X⟧) : K⸨X⸩) = 1 := by
    rw [← map_mul, W.mul_invOfUnit_formalInverseDenom, map_one]
  have hd_ne : ((W.formalInverseDenom : K⟦X⟧) : K⸨X⸩) ≠ 0 := left_ne_zero_of_mul_eq_one hd_mul
  have hinv_mul : ((W.formalInverse : K⟦X⟧) : K⸨X⸩) * ((W.formalInverseDenom : K⟦X⟧) : K⸨X⸩) =
      -((PowerSeries.X : K⟦X⟧) : K⸨X⸩) := by
    rw [W.formalInverse_def, map_neg, map_mul, neg_mul, mul_assoc,
      mul_comm (((PowerSeries.invOfUnit W.formalInverseDenom 1 : K⟦X⟧) : K⸨X⸩)), hd_mul, mul_one]
  have hnegY : φ ((negIsogeny W.toAffine).fieldPullback W.toAffine.genericY) =
      -y * ((W.formalInverseDenom : K⟦X⟧) : K⸨X⸩) := by
    rw [fieldPullback_negIsogeny_genericY, Affine.negY, map_sub, map_sub, map_neg, map_mul]
    have ha₁ : φ (W.toAffine⁄W.toAffine.FunctionField).a₁ = algebraMap K K⸨X⸩ W.a₁ := by
      rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, φ.commutes]
    have ha₃ : φ (W.toAffine⁄W.toAffine.FunctionField).a₃ = algebraMap K K⸨X⸩ W.a₃ := by
      rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₃, φ.commutes]
    simp only [W.formalInverseDenom_def, ha₁, ha₃, map_sub, map_one, map_mul, hX, hW,
      ← LaurentSeries.coe_algebraMap, ← PowerSeries.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply K K⟦X⟧ K⸨X⸩]
    dsimp only [x, y] at hy ⊢
    field_simp
    ring
  rw [map_div₀, map_neg, fieldPullback_negIsogeny_genericX, map_div₀, map_neg, hnegY]
  have hden : -y * ((W.formalInverseDenom : K⟦X⟧) : K⸨X⸩) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hy) hd_ne
  rw [eq_div_iff hden]
  calc
    ((W.formalInverse : K⟦X⟧) : K⸨X⸩) * (-y * ((W.formalInverseDenom : K⟦X⟧) : K⸨X⸩)) =
        (((W.formalInverse : K⟦X⟧) : K⸨X⸩) * ((W.formalInverseDenom : K⟦X⟧) : K⸨X⸩)) * -y := by
      ring
    _ = -(-x / y) * -y := by rw [hinv_mul, hX]
    _ = -x := by field_simp

section PowerSeriesFormalGroup

open scoped PowerSeries.WithPiTopology

/-- Over `K⟦X⟧` with the `(X)`-adic topology, no nonzero formal-group parameter of an elliptic
curve over `K` is fixed by the formal inverse. -/
private theorem formalGroupPoint_ne_neg_of_ne_zero [UniformSpace K] [DiscreteUniformity K]
    [W.IsElliptic] [Fact (IsAdic (Ideal.span {(PowerSeries.X : K⟦X⟧)}))]
    [IsLinearTopology K⟦X⟧ K⟦X⟧]
    (P : FormalGroupPoint (W.baseChange K⟦X⟧) (Ideal.span {(PowerSeries.X : K⟦X⟧)}))
    (hP0 : P ≠ 0) : P ≠ -P := by
  let I : Ideal K⟦X⟧ := Ideal.span {(PowerSeries.X : K⟦X⟧)}
  let W₀ : WeierstrassCurve K⟦X⟧ := W.baseChange K⟦X⟧
  intro hfix
  have ht0 : (P : K⟦X⟧) ≠ 0 := fun h ↦ hP0 (FormalGroupPoint.ext h)
  have h2eq : PowerSeries.C W.a₁ * P + PowerSeries.C W.a₃ * W₀.formalWEval P = 2 := by
    have h := W₀.a₁_mul_add_a₃_mul_formalWEval_eq_two_of_formalInverseEval_eq P.hasEval ht0
      (congrArg FormalGroupPoint.val hfix).symm
    simpa only [W₀, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₃, PowerSeries.algebraMap_eq] using h
  have hP_const : PowerSeries.constantCoeff (P : K⟦X⟧) = 0 :=
    PowerSeries.X_dvd_iff.mp (Ideal.mem_span_singleton.mp P.property)
  -- Away from characteristic `2`, taking constant terms gives `0 = 2`.
  by_cases h2 : (2 : K) = 0
  swap
  · have hW_const : PowerSeries.constantCoeff (W₀.formalWEval P) = 0 :=
      PowerSeries.X_dvd_iff.mp (Ideal.mem_span_singleton.mp
        (by simpa using W₀.formalWEval_mem (I := I) (k := 1) P.hasEval (by simpa using P.property)))
    exact h2 (by simpa [hP_const, hW_const, map_ofNat] using
      (congrArg PowerSeries.constantCoeff h2eq).symm)
  -- In characteristic `2`, ellipticity forces `a₁ ≠ 0` or `a₃ ≠ 0`.
  rw [show (2 : K⟦X⟧) = 0 by rw [← map_ofNat (PowerSeries.C (R := K)) 2, h2, map_zero]] at h2eq
  by_cases ha₁ : W.a₁ = 0
  · -- If `a₁ = 0`, then `a₃ ≠ 0` and `w(P) ≠ 0`, contradicting `a₃ w(P) = 0`.
    have ha₃ : W.a₃ ≠ 0 :=
      (W.a₁_ne_zero_or_a₃_ne_zero_of_Δ_ne_zero_of_two_eq_zero W.isUnit_Δ.ne_zero
        h2).resolve_left (not_not.mpr ha₁)
    rw [ha₁, map_zero, zero_mul, zero_add] at h2eq
    exact mul_ne_zero (by simpa using ha₃) (W₀.formalWEval_ne_zero P.hasEval (pow_ne_zero 3 ht0))
      h2eq
  · -- If `a₁ ≠ 0`, compare `X`-orders: `ord(a₁ P) = ord P < 3 * ord P ≤ ord(a₃ w(P))`.
    have hord_fin : (P : K⟦X⟧).order ≠ ⊤ := PowerSeries.order_eq_top.not.mpr ht0
    have hord_pos : 1 ≤ (P : K⟦X⟧).order :=
      PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hP_const
    have hrhs : 3 * (P : K⟦X⟧).order ≤ (P : K⟦X⟧).order := by
      have hlhs : (PowerSeries.C W.a₁ * (P : K⟦X⟧)).order = (P : K⟦X⟧).order := by
        rw [PowerSeries.order_mul,
          PowerSeries.order_zero_of_isUnit ((IsUnit.mk0 W.a₁ ha₁).map PowerSeries.C), zero_add]
      nth_rw 2 [← hlhs]
      rw [eq_neg_of_add_eq_zero_left h2eq, PowerSeries.order_neg,
        W₀.formalWEval_eq_pow_mul_formalUEval P.hasEval, ← mul_assoc, mul_comm (PowerSeries.C W.a₃),
        mul_assoc, PowerSeries.order_mul, PowerSeries.order_pow, nsmul_eq_mul]
      exact le_add_right le_rfl
    rw [← ENat.natCast_toNat hord_fin] at hord_pos hrhs
    have h1 : 1 ≤ (P : K⟦X⟧).order.toNat := by exact_mod_cast hord_pos
    have h3 : 3 * (P : K⟦X⟧).order.toNat ≤ (P : K⟦X⟧).order.toNat := by exact_mod_cast hrhs
    omega

/-- Auxiliary parameters for `WeierstrassCurve.formalPointHom` over `K⟦X⟧` exist by taking a
strictly higher power of `X`. -/
private theorem exists_aux_formalGroupPoint [UniformSpace K] [DiscreteUniformity K]
    [W.IsElliptic] [Fact (IsAdic (Ideal.span {(PowerSeries.X : K⟦X⟧)}))]
    [IsLinearTopology K⟦X⟧ K⟦X⟧]
    (P : FormalGroupPoint (W.baseChange K⟦X⟧) (Ideal.span {(PowerSeries.X : K⟦X⟧)}))
    (hP : P ≠ -P) :
    ∃ U : FormalGroupPoint (W.baseChange K⟦X⟧) (Ideal.span {(PowerSeries.X : K⟦X⟧)}),
      U ≠ P ∧ U ≠ -P ∧ U ≠ -U := by
  let I : Ideal K⟦X⟧ := Ideal.span {(PowerSeries.X : K⟦X⟧)}
  let W₀ : WeierstrassCurve K⟦X⟧ := W.baseChange K⟦X⟧
  have hP0 : P ≠ 0 := by rintro rfl; exact hP neg_zero.symm
  have ht0 : (P : K⟦X⟧) ≠ 0 := fun h ↦ hP0 (FormalGroupPoint.ext h)
  set m : ℕ := (P : K⟦X⟧).order.toNat + 1
  have hXm_mem : (PowerSeries.X : K⟦X⟧) ^ m ∈ I := by
    rw [Ideal.mem_span_singleton, pow_succ']
    exact dvd_mul_right _ _
  let U : FormalGroupPoint W₀ I := ⟨PowerSeries.X ^ m, hXm_mem⟩
  have hU0 : U ≠ 0 :=
    fun h ↦ pow_ne_zero m PowerSeries.X_ne_zero (congrArg FormalGroupPoint.val h)
  have hordP : (P : K⟦X⟧).order = ((P : K⟦X⟧).order.toNat : ENat) :=
    (ENat.natCast_toNat (PowerSeries.order_eq_top.not.mpr ht0)).symm
  have hord_negP : ((-P : FormalGroupPoint W₀ I) : K⟦X⟧).order = (P : K⟦X⟧).order := by
    rw [FormalGroupPoint.coe_neg, W₀.formalInverseEval_eq P.hasEval, PowerSeries.order_neg,
      PowerSeries.order_mul,
      PowerSeries.order_zero_of_isUnit (W₀.isUnit_formalInverseDenomInvEval P.hasEval), add_zero]
  have hordU : (U : K⟦X⟧).order = (m : ENat) := PowerSeries.order_X_pow m
  have hne_ord : (U : K⟦X⟧).order ≠ (P : K⟦X⟧).order := by
    rw [hordU, hordP, ne_eq, Nat.cast_inj]
    omega
  refine ⟨U, fun h ↦ hne_ord (congrArg (fun Q : FormalGroupPoint W₀ I ↦ (Q : K⟦X⟧).order) h),
    fun h ↦ hne_ord ((congrArg (fun Q : FormalGroupPoint W₀ I ↦ (Q : K⟦X⟧).order) h).trans
      hord_negP), formalGroupPoint_ne_neg_of_ne_zero W U hU0⟩

open scoped Classical in
/-- Under `WeierstrassCurve.formalPointHom` over `K⟦X⟧`, the tautological parameter `X` maps to
the Laurent expansion of the generic point of `W`. -/
private theorem formalPointHom_X_eq_map_genericPoint [UniformSpace K] [DiscreteUniformity K]
    [W.IsElliptic] [Fact (IsAdic (Ideal.span {(PowerSeries.X : K⟦X⟧)}))]
    [IsLinearTopology K⟦X⟧ K⟦X⟧]
    [@IsScalarTower K K K⸨X⸩ Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    (hW : (W.baseChange K⟦X⟧).baseChange K⸨X⸩ = W.baseChange K⸨X⸩)
    [(W.baseChange K⟦X⟧).baseChange K⸨X⸩ |>.IsElliptic] :
    (W.baseChange K⟦X⟧).formalPointHom (S := K⸨X⸩) (Ideal.span {(PowerSeries.X : K⟦X⟧)})
        (exists_aux_formalGroupPoint W) ⟨PowerSeries.X, Ideal.subset_span rfl⟩ =
      AddEquiv.cast (M := fun V : WeierstrassCurve K⸨X⸩ ↦ V.toAffine.Point) hW.symm
        (Affine.Point.map W.functionFieldLaurentExpansion W.toAffine.genericPoint) := by
  let I : Ideal K⟦X⟧ := Ideal.span {(PowerSeries.X : K⟦X⟧)}
  let W₀ : WeierstrassCurve K⟦X⟧ := W.baseChange K⟦X⟧
  let P_X : FormalGroupPoint W₀ I := ⟨PowerSeries.X, Ideal.subset_span rfl⟩
  have hI : IsAdic I := Fact.out
  rw [WeierstrassCurve.formalPointHom_apply, Affine.genericPoint_eq_some, Affine.Point.map_some,
    AddEquiv.cast_apply, Affine.Point.cast_some hW.symm]
  have hWmem : W.formalW ∈ I := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    exact W.constantCoeff_formalW
  have hy : W.functionFieldLaurentExpansion W.toAffine.genericY ≠ 0 :=
    (map_ne_zero_iff W.functionFieldLaurentExpansion
      W.functionFieldLaurentExpansion.injective).mpr W.toAffine.genericY_ne_zero
  refine W₀.formalPoint_eq_some (K := K⸨X⸩) hI P_X.property hWmem _ ?_ ?_
  · dsimp only [P_X]
    rw [LaurentSeries.coe_algebraMap, ← W.functionFieldLaurentExpansion_neg_genericX_div_genericY,
      map_div₀, map_neg, div_mul_cancel₀ _ hy]
  · rw [LaurentSeries.coe_algebraMap, ← W.functionFieldLaurentExpansion_neg_inv_genericY,
      map_neg, map_inv₀, neg_mul, inv_mul_cancel₀ hy]

end PowerSeriesFormalGroup

/-- For a natural number `k` with `ψ_k ≠ 0`, the formal series of `[k]` equals the formal group's
`k`-multiplication series. -/
private theorem formalSeries_mulByIntIsogeny_natCast_aux [W.IsElliptic] {k : ℕ}
    (hk : psiFunctionField W.toAffine k ≠ 0) :
    (mulByIntIsogeny W.toAffine hk).formalSeries = (formalGroup W).nsmulSeries k := by
  open scoped Classical PowerSeries.WithPiTopology in
  let _ : UniformSpace K := ⊥
  have : DiscreteUniformity K := ⟨rfl⟩
  let I : Ideal K⟦X⟧ := Ideal.span {(PowerSeries.X : K⟦X⟧)}
  have hI : IsAdic I := PowerSeries.WithPiTopology.isAdic_span_X
  have : Fact (IsAdic I) := ⟨hI⟩
  have : IsLinearTopology K⟦X⟧ K⟦X⟧ := hI.isLinearTopology
  let W₀ : WeierstrassCurve K⟦X⟧ := W.baseChange K⟦X⟧
  have hW : W₀.baseChange K⸨X⸩ = W.baseChange K⸨X⸩ := by
    simp only [W₀, WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
    rw [IsScalarTower.algebraMap_eq K K⟦X⟧ K⸨X⸩]
  have : (W₀.baseChange K⸨X⸩).IsElliptic := hW ▸ inferInstance
  let e := AddEquiv.cast (M := fun V : WeierstrassCurve K⸨X⸩ ↦ V.toAffine.Point) hW.symm
  have : @IsScalarTower K K K⸨X⸩ Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    .of_algebraMap_eq fun _ ↦ rfl
  let P_X : FormalGroupPoint W₀ I := ⟨PowerSeries.X, Ideal.subset_span rfl⟩
  -- Taking `k`-multiples matches `k • P_X` with the pullback of `[k]`.
  have hk_img : W₀.formalPointHom (S := K⸨X⸩) I (exists_aux_formalGroupPoint W) (k • P_X) =
      e (Affine.Point.map W.functionFieldLaurentExpansion
        (Affine.Point.map (mulByIntIsogeny W.toAffine hk).fieldPullback
          W.toAffine.genericPoint)) := by
    rw [map_nsmul, formalPointHom_X_eq_map_genericPoint W hW, ← map_nsmul, ← map_nsmul,
      ← natCast_zsmul, ← map_mulByIntIsogeny_genericPoint W.toAffine hk]
  -- Extract the parameter `-x / y` from both sides.
  have hparam :=
    congrArg (fun Q : (W₀.baseChange K⸨X⸩).toAffine.Point ↦ -Q.xCoord / Q.yCoord) hk_img
  simp only [e, WeierstrassCurve.formalPointHom_apply,
    W₀.neg_xCoord_div_yCoord_formalPoint (K := K⸨X⸩) hI, AddEquiv.cast_apply,
    Affine.Point.xCoord_cast hW.symm, Affine.Point.yCoord_cast hW.symm,
    Affine.Point.xCoord_map, Affine.Point.yCoord_map,
    Affine.xCoord_genericPoint, Affine.yCoord_genericPoint, LaurentSeries.coe_algebraMap] at hparam
  -- Identify the parameter of `k • P_X` with `(formalGroup W).nsmulSeries k`.
  have hmul_val : ((k • P_X : FormalGroupPoint W₀ I) : K⟦X⟧) = (formalGroup W).nsmulSeries k := by
    rw [FormalGroupPoint.coe_nsmul]
    have hmap : (formalGroup W₀).nsmulSeries k =
        ((formalGroup W).nsmulSeries k).map PowerSeries.C := by
      simp only [W₀, WeierstrassCurve.baseChange, WeierstrassCurve.map_formalGroup,
        ← FormalGroup.map_nsmulSeries, PowerSeries.algebraMap_eq]
    rw [hmap, PowerSeries.eval₂_map continuous_id PowerSeries.WithPiTopology.continuous_C
      PowerSeries.HasEval.X, RingHom.id_comp, PowerSeries.eval₂_C_X]
  rw [hmul_val] at hparam
  refine (formalSeries_eq_iff _ _).mpr ?_
  simpa only [map_div₀, map_neg] using hparam

/-- **The formal power series of `[n]` is the formal group's integer multiplication series.** -/
@[simp]
theorem formalSeries_mulByIntIsogeny [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W.toAffine n ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalSeries = (formalGroup W).zsmulSeries n := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · rw [FormalGroup.zsmulSeries_natCast]
    exact formalSeries_mulByIntIsogeny_natCast_aux W hn
  · have hk0 : (k : ℤ) ≠ 0 := by
      intro h
      rw [h, neg_zero] at hn
      exact hn (by simp [psiFunctionField_def])
    have hk : psiFunctionField W.toAffine k ≠ 0 :=
      psiFunctionField_ne_zero_of_Δ_ne_zero W.toAffine W.toAffine.isUnit_Δ.ne_zero hk0
    rw [← negIsogeny_comp_mulByIntIsogeny W.toAffine hk hn, formalSeries_comp,
      formalSeries_negIsogeny, formalSeries_mulByIntIsogeny_natCast_aux W hk,
      FormalGroup.zsmulSeries_neg, FormalGroup.zsmulSeries_natCast]

end TauCeti.Isogeny
