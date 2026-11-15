/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.FormalSeries
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Hom
public import TauCeti.RingTheory.FormalGroup.ZSMul
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Projective

/-!
# Formal-group addition and multiplication by `n` for morphisms of elliptic curves

An isogeny `φ : W₁ → W₂` of Weierstrass curves over a field `K` expands at infinity in the local
parameter `z = -x / y` to a power series `φ.formalSeries ∈ K⟦X⟧`
(`TauCeti.Isogeny.formalSeries`), extended by `0` to the pointed-morphism carrier `Hom W₁ W₂`
(`TauCeti.Isogeny.Hom.formalSeries`). This file connects that expansion to the formal group law
`formalGroup W₂`:

1. **Negation.** Without any ellipticity assumption on `W` or `W₂`, the negation isogeny
   `negIsogeny W` induces the formal inverse `(formalGroup W).addInvX`
   (`TauCeti.Isogeny.formalSeries_negIsogeny`), and negating a morphism `f : Hom W₁ W₂` composes
   `f.formalSeries` with `(formalGroup W₂).addInvX` (`TauCeti.Isogeny.Hom.formalSeries_neg`).

2. **Addition and scalar multiplication.** When `W₂` is elliptic, the Bosma–Lenstra projective
   addition law `dblAddXYZ` evaluated at the formal points `[q : -1 : w(q)]` over `K⸨X⸩`
   (`WeierstrassCurve.formalThetaPoint_add`) shows that `(f + g).formalSeries` is the formal-group
   sum of `f.formalSeries` and `g.formalSeries` in `formalGroup W₂`
   (`TauCeti.Isogeny.Hom.formalSeries_add`). Packaging this as an additive homomorphism
   `Hom.toFormalGroupPoint : Hom W₁ W₂ →+ (formalGroup W₂).Point Unit` gives the formal series of
   natural and integer multiples of morphisms (`TauCeti.Isogeny.Hom.formalSeries_nsmul`,
   `TauCeti.Isogeny.Hom.formalSeries_zsmul`).

3. **Multiplication by `n`.** For an elliptic curve `W` over `K`, the multiplication-by-`n` isogeny
   induces `(formalGroup W).zsmulSeries n` (`TauCeti.Isogeny.formalSeries_mulByIntIsogeny`).
   Combining this with `TauCeti.Isogeny.order_formalSeries` identifies the order of
   `(formalGroup W).nsmulSeries n` with the inseparable degree of `[n]`
   (`WeierstrassCurve.order_nsmulSeries_formalGroup`), in every characteristic and without assuming
   `K` is perfect, and base-changing to residue fields shows `[n]` on `formalGroup W` is nonzero
   for `n ≠ 0` over any nontrivial commutative ring.

## Main definitions

* `TauCeti.Isogeny.Hom.toFormalGroupPoint`: for an elliptic target `W₂`, the additive homomorphism
  sending `f : Hom W₁ W₂` to `f.formalSeries` as a `1`-variable point of `formalGroup W₂`.

## Main results

* `TauCeti.Isogeny.formalSeries_negIsogeny` and `TauCeti.Isogeny.Hom.formalSeries_neg`: negation
  induces `(formalGroup W).addInvX`.
* `TauCeti.Isogeny.Hom.formalSeries_add`, `TauCeti.Isogeny.Hom.formalSeries_nsmul`, and
  `TauCeti.Isogeny.Hom.formalSeries_zsmul`: compatibility of `Hom.formalSeries` with the formal
  group law of an elliptic target `W₂`.
* `TauCeti.Isogeny.formalSeries_mulByIntIsogeny`: for an elliptic curve `W`, multiplication by `n`
  induces `(formalGroup W).zsmulSeries n`.
* `WeierstrassCurve.order_zsmulSeries_formalGroup` and
  `WeierstrassCurve.order_nsmulSeries_formalGroup`: for an elliptic curve `W` over a field and
  `n ≠ 0`, the order of `[n]` on `formalGroup W` equals the inseparable degree of `[n]`.
* `WeierstrassCurve.zsmulSeries_formalGroup_ne_zero`,
  `WeierstrassCurve.zsmulSeries_formalGroup_eq_zero_iff`,
  `WeierstrassCurve.nsmulSeries_formalGroup_ne_zero`, and
  `WeierstrassCurve.nsmulSeries_formalGroup_eq_zero_iff`: for an elliptic curve `W` over a
  nontrivial commutative ring, `[n]` on `formalGroup W` vanishes if and only if `n = 0`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, IV.2 and IV.4.
-/

public section

open WeierstrassCurve HahnSeries MvPowerSeries
open scoped LaurentSeries PowerSeries

namespace TauCeti.Isogeny

/-! ### Negation on arbitrary Weierstrass curves -/

section Negation

variable {K : Type*} [Field K]

/-- **The negation isogeny induces the formal inverse `(formalGroup W).addInvX`** on any
Weierstrass curve over a field (Silverman IV.1 and IV.4). -/
@[simp]
theorem formalSeries_negIsogeny (W : WeierstrassCurve K) :
    (negIsogeny W.toAffine).formalSeries = (formalGroup W).addInvX := by
  apply (formalSeries_eq_iff _ _).mpr
  rw [W.formalGroup_addInvX, W.formalInverse_def]
  set E := W.functionFieldLaurentExpansion
  have hy : E W.toAffine.genericY ≠ 0 := W.functionFieldLaurentExpansion_genericY_ne_zero
  have hx : E W.toAffine.genericX = -(((PowerSeries.X : K⟦X⟧) : K⸨X⸩) * E W.toAffine.genericY) :=
    W.functionFieldLaurentExpansion_genericX_eq_neg_X_mul_functionFieldLaurentExpansion_genericY
  have hw : E W.toAffine.genericY * (W.formalW : K⸨X⸩) = -1 :=
    W.functionFieldLaurentExpansion_genericY_mul_formalW
  have hd : (W.formalInverseDenom : K⸨X⸩) *
      (PowerSeries.invOfUnit W.formalInverseDenom 1 : K⸨X⸩) = 1 := by
    simpa only [map_mul, map_one] using
      congrArg (ofPowerSeries ℤ K) W.mul_invOfUnit_formalInverseDenom
  -- Expand `[-1]* y = -y - a₁ x - a₃ = -y (1 - a₁ X - a₃ w)`.
  have hden : E ((negIsogeny W.toAffine).fieldPullback W.toAffine.genericY) =
      -E W.toAffine.genericY * (W.formalInverseDenom : K⸨X⸩) := by
    rw [fieldPullback_negIsogeny_genericY, Affine.negY, map_sub, map_sub, map_mul, map_neg]
    simp only [Affine.baseChange_a₁, Affine.baseChange_a₃, AlgHom.commutes]
    rw [W.formalInverseDenom_def, map_sub, map_sub, map_one, map_mul, map_mul, hx,
      PowerSeries.C_eq_algebraMap, PowerSeries.C_eq_algebraMap,
      ← _root_.LaurentSeries.coe_algebraMap,
      ← IsScalarTower.algebraMap_apply K K⟦X⟧ K⸨X⸩,
      ← IsScalarTower.algebraMap_apply K K⟦X⟧ K⸨X⸩,
      _root_.LaurentSeries.coe_algebraMap]
    linear_combination -(algebraMap K K⸨X⸩ W.a₃) * hw
  have hden0 : -E W.toAffine.genericY * (W.formalInverseDenom : K⸨X⸩) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hy) (left_ne_zero_of_mul_eq_one hd)
  rw [map_div₀ ((negIsogeny W.toAffine).fieldPullback),
    map_neg ((negIsogeny W.toAffine).fieldPullback), fieldPullback_negIsogeny_genericX,
    map_div₀ E, map_neg E, hden, hx, neg_neg, map_neg (ofPowerSeries ℤ K),
    map_mul (ofPowerSeries ℤ K), eq_div_iff hden0]
  linear_combination ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) * E W.toAffine.genericY * hd

/-- **Negation of a morphism composes its formal series with the formal inverse of `W₂`.** -/
@[simp]
theorem Hom.formalSeries_neg {W₁ W₂ : WeierstrassCurve K} (f : Hom W₁.toAffine W₂.toAffine) :
    (-f).formalSeries = PowerSeries.subst f.formalSeries (formalGroup W₂).addInvX := by
  rw [Hom.neg_def, Hom.formalSeries_comp, Hom.formalSeries_ofIsogeny, formalSeries_negIsogeny]

end Negation

/-! ### Formal-group addition and scalar multiplication on `Hom` -/

namespace Hom

section Addition

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]

private theorem map_baseChange_functionFieldLaurentExpansion_eq_fracCurve
    (W₁ W₂ : WeierstrassCurve K) :
    (W₂.toAffine⁄W₁.toAffine.FunctionField).map W₁.functionFieldLaurentExpansion.toRingHom =
      fracCurve W₂ Unit K⸨X⸩ := by
  have hcomp : W₁.functionFieldLaurentExpansion.toRingHom.comp
      (algebraMap K W₁.toAffine.FunctionField) =
      (algebraMap (MvPowerSeries Unit K) K⸨X⸩).comp (algebraMap K (MvPowerSeries Unit K)) :=
    RingHom.ext fun c ↦ (W₁.functionFieldLaurentExpansion.commutes c).trans
      (IsScalarTower.algebraMap_apply K K⟦X⟧ K⸨X⸩ c)
  exact ((W₂.map_map _ _).trans (congrArg W₂.map hcomp)).trans (fracCurve_def W₂ Unit K⸨X⸩).symm

open scoped Classical in
-- Transporting `f.tautologicalPoint` along Laurent expansion at infinity on `W₁` yields the
-- formal point `[f.formalSeries : -1 : w₂(f.formalSeries)]` on `W₂` over `K⸨X⸩`.
private theorem map_functionFieldLaurentExpansion_tautologicalPoint
    (f : Hom W₁.toAffine W₂.toAffine) :
    Affine.Point.mapAlong W₁.functionFieldLaurentExpansion.toRingHom
        W₁.functionFieldLaurentExpansion.toRingHom.injective f.tautologicalPoint =
      AddEquiv.cast (M := fun V : WeierstrassCurve K⸨X⸩ ↦ V.toAffine.Point)
        (map_baseChange_functionFieldLaurentExpansion_eq_fracCurve W₁ W₂).symm
        (W₂.formalThetaPoint K⸨X⸩ f.formalSeries) := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · rw [tautologicalPoint_zero, Affine.Point.mapAlong_zero, formalSeries_zero,
      W₂.formalThetaPoint_zero K⸨X⸩, _root_.map_zero]
  · have hΔ := W₂.fracCurve_Δ_ne_zero (σ := Unit) (KK := K⸨X⸩) W₂.isUnit_Δ.ne_zero
    obtain ⟨hns, hθ⟩ := W₂.formalThetaPoint_eq_some hΔ φ.constantCoeff_formalSeries
      φ.formalSeries_ne_zero
    rw [formalSeries_ofIsogeny, hθ, AddEquiv.cast_apply,
      Affine.Point.cast_some (map_baseChange_functionFieldLaurentExpansion_eq_fracCurve W₁ W₂).symm,
      tautologicalPoint_ofIsogeny, Isogeny.tautologicalPoint_eq_map_genericPoint,
      Affine.genericPoint_eq_some, Affine.Point.map_some, Affine.Point.mapAlong_some]
    -- Invert `-1 / y₂ ↦ w₂(φ.formalSeries)` and `-x₂ / y₂ ↦ φ.formalSeries` to read off `(x₂, y₂)`.
    have hY : W₁.functionFieldLaurentExpansion (φ.fieldPullback W₂.toAffine.genericY) =
        -1 / algebraMap (MvPowerSeries Unit K) K⸨X⸩
          (PowerSeries.subst φ.formalSeries W₂.formalW) := by
      have hw := φ.coe_subst_formalW_formalSeries
      simp only [_root_.map_neg, map_inv₀] at hw
      have h0 : algebraMap (MvPowerSeries Unit K) K⸨X⸩
          (PowerSeries.subst φ.formalSeries W₂.formalW) ≠ 0 :=
        W₂.algebraMap_subst_formalW_ne_zero φ.constantCoeff_formalSeries φ.formalSeries_ne_zero
      rw [_root_.LaurentSeries.coe_algebraMap] at h0
      rw [_root_.LaurentSeries.coe_algebraMap, eq_div_iff h0]
      have hw' : -((W₁.functionFieldLaurentExpansion (φ.fieldPullback W₂.toAffine.genericY))⁻¹) =
          ((PowerSeries.subst φ.formalSeries W₂.formalW : K⟦X⟧) : K⸨X⸩) := hw.symm
      have hy0 : W₁.functionFieldLaurentExpansion (φ.fieldPullback W₂.toAffine.genericY) ≠ 0 := by
        intro hz
        rw [hz, inv_zero, _root_.neg_zero] at hw'
        exact h0 hw'.symm
      linear_combination
        -(W₁.functionFieldLaurentExpansion (φ.fieldPullback W₂.toAffine.genericY)) * hw' -
          inv_mul_cancel₀ hy0
    have hX : W₁.functionFieldLaurentExpansion (φ.fieldPullback W₂.toAffine.genericX) =
        algebraMap (MvPowerSeries Unit K) K⸨X⸩ φ.formalSeries /
          algebraMap (MvPowerSeries Unit K) K⸨X⸩
            (PowerSeries.subst φ.formalSeries W₂.formalW) := by
      have hp := φ.coe_formalSeries
      simp only [map_div₀, _root_.map_neg, hY] at hp
      have h0 : algebraMap (MvPowerSeries Unit K) K⸨X⸩
          (PowerSeries.subst φ.formalSeries W₂.formalW) ≠ 0 :=
        W₂.algebraMap_subst_formalW_ne_zero φ.constantCoeff_formalSeries φ.formalSeries_ne_zero
      rw [_root_.LaurentSeries.coe_algebraMap] at hp h0 ⊢
      rw [div_eq_mul_inv (-1), neg_one_mul, div_neg, div_inv_eq_mul, neg_mul, neg_neg] at hp
      exact (eq_div_iff h0).mpr hp.symm
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hX, hY]

/-- **For an elliptic target `W₂`, addition of morphisms induces formal-group addition of their
formal series.** -/
theorem formalSeries_add (f g : Hom W₁.toAffine W₂.toAffine) :
    (f + g).formalSeries =
      subst ![f.formalSeries, g.formalSeries] (formalGroup W₂).toPowerSeries := by
  classical
  have hΔ := W₂.fracCurve_Δ_ne_zero (σ := Unit) (KK := K⸨X⸩) W₂.isUnit_Δ.ne_zero
  have hfg0 : ∀ i : Fin 2, constantCoeff (![f.formalSeries, g.formalSeries] i) = 0 :=
    Fin.forall_fin_two.mpr ⟨f.constantCoeff_formalSeries, g.constantCoeff_formalSeries⟩
  refine (W₂.formalThetaPoint_inj hΔ (f + g).constantCoeff_formalSeries
    (constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hfg0) hfg0
      (formalGroup W₂).zero_constantCoeff)).mp ?_
  rw [← W₂.formalThetaPoint_add hΔ f.constantCoeff_formalSeries g.constantCoeff_formalSeries]
  have hf := map_functionFieldLaurentExpansion_tautologicalPoint f
  have hg := map_functionFieldLaurentExpansion_tautologicalPoint g
  have hfg := map_functionFieldLaurentExpansion_tautologicalPoint (f + g)
  rw [tautologicalPoint_add, Affine.Point.mapAlong_add, hf, hg, ← _root_.map_add] at hfg
  exact ((AddEquiv.cast _).injective hfg).symm

/-- **For an elliptic target `W₂`, the formal series of morphisms `W₁ → W₂` as an additive
homomorphism into `1`-variable points of `formalGroup W₂`.** -/
noncomputable def toFormalGroupPoint :
    Hom W₁.toAffine W₂.toAffine →+ (formalGroup W₂).Point Unit where
  toFun f := ⟨f.formalSeries, .of_constantCoeff_zero f.constantCoeff_formalSeries⟩
  map_zero' := Subtype.ext formalSeries_zero
  map_add' f g := Subtype.ext (formalSeries_add f g)

/-- The underlying power series of `f.toFormalGroupPoint` is `f.formalSeries`. -/
@[simp]
theorem val_toFormalGroupPoint (f : Hom W₁.toAffine W₂.toAffine) :
    (f.toFormalGroupPoint).val = f.formalSeries := (rfl)

/-- `Hom.toFormalGroupPoint` is injective. -/
theorem toFormalGroupPoint_injective :
    Function.Injective (toFormalGroupPoint (W₁ := W₁) (W₂ := W₂)) :=
  fun _ _ h ↦ formalSeries_injective (congrArg Subtype.val h)

/-- Two morphisms give the same formal-group point if and only if they are equal. -/
@[simp]
theorem toFormalGroupPoint_inj {f g : Hom W₁.toAffine W₂.toAffine} :
    f.toFormalGroupPoint = g.toFormalGroupPoint ↔ f = g :=
  toFormalGroupPoint_injective.eq_iff

/-- A morphism's formal-group point is zero if and only if the morphism is zero. -/
@[simp]
theorem toFormalGroupPoint_eq_zero_iff {f : Hom W₁.toAffine W₂.toAffine} :
    f.toFormalGroupPoint = 0 ↔ f = 0 :=
  _root_.map_eq_zero_iff toFormalGroupPoint toFormalGroupPoint_injective

/-- The identity morphism of an elliptic curve maps to the tautological point `X` of its formal
group. -/
@[simp]
theorem toFormalGroupPoint_id (W : WeierstrassCurve K) [W.IsElliptic] :
    (Hom.id W.toAffine).toFormalGroupPoint = (formalGroup W).tautologicalPoint :=
  Subtype.ext ((val_toFormalGroupPoint _).trans
    ((formalSeries_id W).trans (formalGroup W).val_tautologicalPoint.symm))

/-- **For an elliptic target `W₂`, natural scalar multiplication of a morphism composes its formal
series with `nsmulSeries n`.** -/
@[simp]
theorem formalSeries_nsmul (n : ℕ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalSeries = PowerSeries.subst f.formalSeries ((formalGroup W₂).nsmulSeries n) := by
  have h := congrArg Subtype.val (_root_.map_nsmul (toFormalGroupPoint (W₁ := W₁) (W₂ := W₂)) n f)
  simpa only [val_toFormalGroupPoint, ← (formalGroup W₂).subst_nsmulSeries] using h

/-- **For an elliptic target `W₂`, integer scalar multiplication of a morphism composes its formal
series with `zsmulSeries n`.** -/
@[simp]
theorem formalSeries_zsmul (n : ℤ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalSeries = PowerSeries.subst f.formalSeries ((formalGroup W₂).zsmulSeries n) := by
  have h := congrArg Subtype.val (_root_.map_zsmul (toFormalGroupPoint (W₁ := W₁) (W₂ := W₂)) n f)
  simpa only [val_toFormalGroupPoint, ← (formalGroup W₂).subst_zsmulSeries] using h

end Addition

section EndRing

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- For an elliptic curve `W`, the natural-number endomorphism `(n : Hom W W)` induces
`(formalGroup W).nsmulSeries n`. -/
@[simp]
theorem formalSeries_natCast (n : ℕ) :
    (n : Hom W.toAffine W.toAffine).formalSeries = (formalGroup W).nsmulSeries n := by
  rw [← nsmul_one, formalSeries_nsmul, Hom.one_def, formalSeries_id, PowerSeries.X_subst]

/-- For an elliptic curve `W`, the integer endomorphism `(n : Hom W W)` induces
`(formalGroup W).zsmulSeries n`. -/
@[simp]
theorem formalSeries_intCast (n : ℤ) :
    (n : Hom W.toAffine W.toAffine).formalSeries = (formalGroup W).zsmulSeries n := by
  rw [← zsmul_one, formalSeries_zsmul, Hom.one_def, formalSeries_id, PowerSeries.X_subst]

end EndRing

end Hom

/-! ### Multiplication-by-`n` isogenies on the formal group -/

section MulByInt

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **For an elliptic curve `W`, the multiplication-by-`n` isogeny induces
`(formalGroup W).zsmulSeries n` on the formal parameter** (Silverman IV.4). -/
@[simp]
theorem formalSeries_mulByIntIsogeny {n : ℤ} (hn : psiFunctionField W.toAffine n ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalSeries = (formalGroup W).zsmulSeries n := by
  rw [← Hom.formalSeries_ofIsogeny, ofIsogeny_mulByIntIsogeny, Hom.formalSeries_zsmul,
    Hom.formalSeries_id, PowerSeries.X_subst]

/-- **For an elliptic curve `W` over a field and `n ≠ 0`, the order of
`(formalGroup W).zsmulSeries n` equals the inseparable degree of `[n]`.** -/
theorem _root_.WeierstrassCurve.order_zsmulSeries_formalGroup {n : ℤ} (hn : n ≠ 0) :
    ((formalGroup W).zsmulSeries n).order =
      (mulByIntIsogenyOfNeZero W.toAffine hn).inseparableDegree := by
  rw [← formalSeries_mulByIntIsogeny W _, order_formalSeries]

/-- **For an elliptic curve `W` over a field and `n ≠ 0`, the order of
`(formalGroup W).nsmulSeries n` equals the inseparable degree of `[n]`.** -/
theorem _root_.WeierstrassCurve.order_nsmulSeries_formalGroup {n : ℕ} (hn : n ≠ 0) :
    ((formalGroup W).nsmulSeries n).order =
      (mulByIntIsogenyOfNeZero W.toAffine (Nat.cast_ne_zero.mpr hn)).inseparableDegree := by
  rw [← FormalGroup.zsmulSeries_natCast, W.order_zsmulSeries_formalGroup (Nat.cast_ne_zero.mpr hn)]

end MulByInt

section NontrivialRing

variable {R : Type*} [CommRing R] [Nontrivial R] (W : WeierstrassCurve R) [W.IsElliptic]

/-- **For an elliptic curve `W` over a nontrivial commutative ring and `n ≠ 0`,
`(formalGroup W).zsmulSeries n` is nonzero**, in every characteristic. -/
theorem _root_.WeierstrassCurve.zsmulSeries_formalGroup_ne_zero {n : ℤ} (hn : n ≠ 0) :
    (formalGroup W).zsmulSeries n ≠ 0 := by
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal R
  let : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  intro h0
  have hmap : (formalGroup (W.map (Ideal.Quotient.mk 𝔪))).zsmulSeries n = 0 := by
    rw [W.map_formalGroup, ← (formalGroup W).map_zsmulSeries, h0, map_zero]
  have hfield :=
    (mulByIntIsogenyOfNeZero (W.map (Ideal.Quotient.mk 𝔪)).toAffine hn).formalSeries_ne_zero
  rw [formalSeries_mulByIntIsogeny (W.map (Ideal.Quotient.mk 𝔪)) _] at hfield
  exact hfield hmap

/-- **For an elliptic curve `W` over a nontrivial commutative ring,
`(formalGroup W).zsmulSeries n = 0` if and only if `n = 0`.** -/
@[simp]
theorem _root_.WeierstrassCurve.zsmulSeries_formalGroup_eq_zero_iff {n : ℤ} :
    (formalGroup W).zsmulSeries n = 0 ↔ n = 0 :=
  ⟨fun h ↦ by_contra fun hn ↦ W.zsmulSeries_formalGroup_ne_zero hn h,
    fun h ↦ by simp [h]⟩

/-- **For an elliptic curve `W` over a nontrivial commutative ring and `n ≠ 0`,
`(formalGroup W).nsmulSeries n` is nonzero**, in every characteristic. -/
theorem _root_.WeierstrassCurve.nsmulSeries_formalGroup_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (formalGroup W).nsmulSeries n ≠ 0 := by
  rw [← FormalGroup.zsmulSeries_natCast]
  exact W.zsmulSeries_formalGroup_ne_zero (Nat.cast_ne_zero.mpr hn)

/-- **For an elliptic curve `W` over a nontrivial commutative ring,
`(formalGroup W).nsmulSeries n = 0` if and only if `n = 0`.** -/
@[simp]
theorem _root_.WeierstrassCurve.nsmulSeries_formalGroup_eq_zero_iff {n : ℕ} :
    (formalGroup W).nsmulSeries n = 0 ↔ n = 0 :=
  ⟨fun h ↦ by_contra fun hn ↦ W.nsmulSeries_formalGroup_ne_zero hn h,
    fun h ↦ by simp [h]⟩

end NontrivialRing

end TauCeti.Isogeny
