/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Add
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.MapsInfinity
public import TauCeti.RingTheory.FormalGroup.Hom.Basic
public import TauCeti.RingTheory.FormalGroup.ZSMul
-- Proof-only: morphisms act additively on points over every field.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring
-- Proof-only: the source of an isogeny to an elliptic curve is elliptic.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic
-- Proof-only: `[n] = n • id` in `Hom W W`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Hom
-- Proof-only: the Bosma–Lenstra addition law and parametrized formal points.
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.FormalPoint
-- Proof-only: multivariate power series over a domain form a domain.
import TauCeti.RingTheory.MvPowerSeries.NonZeroDivisors

/-!
# Formal group homomorphisms and additive formal series of elliptic curve morphisms

Let `W₁` and `W₂` be elliptic Weierstrass curves over a field `K`. Expanding the pulled-back
formal parameter `-x₂ / y₂` at infinity attaches to each isogeny `φ : W₁ → W₂` a formal power
series `φ.formalSeries ∈ K⟦X⟧` (`TauCeti.Isogeny.formalSeries`). Extending this assignment by `0`
on the zero morphism gives `TauCeti.Isogeny.Hom.formalSeries` on the full additive group
`Hom W₁.toAffine W₂.toAffine`.

This file proves two compatibilities between the group laws of `W₁` and `W₂` and the formal group
laws `formalGroup W₁` and `formalGroup W₂`:

1. **Additivity in the morphism (`Hom.formalSeries_add`).** Combining
   `WeierstrassCurve.formalParamPoint_subst_pair_formalAdd` (from
   `Scheme/Addition/FormalPoint.lean`) with `WeierstrassCurve.subst_formalGroup_toPowerSeries`
   identifies formal-group addition on `formalGroup W₂` with point addition on `W₂` over the
   fraction field of the power-series ring, with no case splits on coinciding or opposite
   parameters. Reading the tautological point of `f : Hom W₁ W₂` in `K⸨X⸩` therefore turns
   `Hom.formalSeries` into an additive homomorphism
   `Hom W₁.toAffine W₂.toAffine →+ (formalGroup W₂).Point Unit`
   (`TauCeti.Isogeny.Hom.formalSeriesPointHom`). In particular, negation is `formalInverse` and
   multiplication by `n : ℤ` has formal series `(formalGroup W).zsmulSeries n`
   (`TauCeti.Isogeny.formalSeries_mulByIntIsogeny`).
2. **The formal group homomorphism of an isogeny (`Isogeny.formalGroupHom`).** Evaluating `φ` over
   the fraction field of `MvPowerSeries (Fin 2) K` at the generic formal parameters `X 0`, `X 1`,
   and `(formalGroup W₁).toPowerSeries`, where `(φ.map ι).pointMap` is additive by
   `TauCeti.Isogeny.Hom.pointMap_add`, shows that `φ.formalSeries` satisfies the homomorphism
   equation `φ(F₁(X, Y)) = F₂(φ(X), φ(Y))`, packaging every isogeny and morphism as a bundled
   `TauCeti.FormalGroupHom`.

## Main definitions

* `TauCeti.Isogeny.Hom.formalSeries`: the formal series of a morphism (`0` on `0`, `φ.formalSeries`
  on `ofIsogeny φ`).
* `TauCeti.Isogeny.Hom.formalSeriesPointHom`: `Hom W₁.toAffine W₂.toAffine →+
  (formalGroup W₂).Point Unit`.
* `TauCeti.Isogeny.formalGroupHom` and `TauCeti.Isogeny.Hom.formalGroupHom`: the bundled
  `FormalGroupHom (formalGroup W₁) (formalGroup W₂)` induced by an isogeny or morphism.

## Main results

* `TauCeti.Isogeny.Hom.formalSeries_injective`: a morphism is determined by its formal series.
* `TauCeti.Isogeny.Hom.formalSeries_add`, `formalSeries_sub`, `formalSeries_neg`,
  `formalSeries_nsmul`, `formalSeries_zsmul`: compatibility of `Hom.formalSeries` with the group
  operations on `Hom`.
* `TauCeti.Isogeny.formalSeries_negIsogeny` and `TauCeti.Isogeny.formalGroupHom_negIsogeny`:
  `[-1]` has formal series `W.formalInverse` and induces `(formalGroup W).zsmulHom (-1)`.
* `TauCeti.Isogeny.formalSeries_mulByIntIsogeny`,
  `TauCeti.Isogeny.formalSeries_mulByIntIsogeny_natCast`, and
  `TauCeti.Isogeny.formalGroupHom_mulByIntIsogeny`: `[n]` has formal series
  `(formalGroup W).zsmulSeries n` and induces `(formalGroup W).zsmulHom n`.
* `TauCeti.Isogeny.subst_formalGroup_formalSeries`: `φ(F₁(X, Y)) = F₂(φ(X), φ(Y))`.
* `TauCeti.Isogeny.Hom.formalGroupHom_neg`, `Hom.formalGroupHom_nsmul`,
  `Hom.formalGroupHom_zsmul`, and the `Hom.formalGroupHom_*_applyPoint` lemmas: compatibility of
  `Hom.formalGroupHom` with the additive group structure on `Hom` and its action on formal points.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, IV.2, and IV.4.
-/

public section

open MvPowerSeries Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped LaurentSeries PowerSeries Polynomial.Bivariate

namespace TauCeti

namespace Isogeny

variable {K : Type*} [Field K] {W₁ W₂ W₃ : WeierstrassCurve K}

open scoped Classical in
/-- Evaluating the tautological point of `ψ : W₁ → W₂` along
`LaurentSeries.mvSubstAlgHom hq hq0 ∘ W₁.functionFieldLaurentExpansion` in any fraction field `KK`
of `MvPowerSeries σ K` gives `W₂.formalParamPoint (PowerSeries.subst q ψ.formalSeries)`. -/
private theorem point_map_mvSubstAlgHom_tautologicalPoint [W₂.IsElliptic]
    (ψ : Isogeny W₁.toAffine W₂.toAffine) {σ : Type*} {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0)
    {KK : Type*} [Field KK] [Algebra K KK] [Algebra (MvPowerSeries σ K) KK]
    [IsScalarTower K (MvPowerSeries σ K) KK] [IsFractionRing (MvPowerSeries σ K) KK] :
    Point.map ((LaurentSeries.mvSubstAlgHom (L := KK) hq hq0).comp
        W₁.functionFieldLaurentExpansion) ψ.pullback.tautologicalPoint =
      W₂.formalParamPoint (KK := KK) (PowerSeries.subst q ψ.formalSeries) := by
  have hqc : constantCoeff (PowerSeries.subst q ψ.formalSeries) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hq _ ψ.constantCoeff_formalSeries
  have hqψ0 : PowerSeries.subst q ψ.formalSeries ≠ 0 :=
    (PowerSeries.subst_eq_zero_iff hq hq0).not.mpr ψ.formalSeries_ne_zero
  obtain ⟨_, hparam⟩ := W₂.exists_formalParamPoint_eq_some_of_algebraMap_ne_zero (KK := KK)
    (.of_constantCoeff_zero hqc) ((map_ne_zero_iff _ (IsFractionRing.injective _ KK)).mpr hqψ0)
  rw [Isogeny.tautologicalPoint_eq_map_genericPoint, Point.map_map, hparam, genericPoint_eq_some,
    Point.map_some]
  refine Point.eq_of_coords (Point.some_ne_zero _) (Point.some_ne_zero _) ?_ ?_
  · simp only [Point.xCoord_some, AlgHom.comp_apply,
      ψ.functionFieldLaurentExpansion_fieldPullback,
      W₂.functionFieldLaurentExpansion_genericX_eq_X_div_formalW, map_div₀,
      LaurentSeries.substAlgHom_coe,
      PowerSeries.subst_X (.of_constantCoeff_zero' ψ.constantCoeff_formalSeries),
      LaurentSeries.mvSubstAlgHom_coe,
      PowerSeries.subst_comp_subst_apply (.of_constantCoeff_zero ψ.constantCoeff_formalSeries)
        (.of_constantCoeff_zero hq)]
  · simp only [Point.yCoord_some, AlgHom.comp_apply,
      ψ.functionFieldLaurentExpansion_fieldPullback,
      W₂.functionFieldLaurentExpansion_genericY_eq_neg_one_div_formalW, map_div₀, map_neg,
      map_one, LaurentSeries.substAlgHom_coe, LaurentSeries.mvSubstAlgHom_coe,
      PowerSeries.subst_comp_subst_apply (.of_constantCoeff_zero ψ.constantCoeff_formalSeries)
        (.of_constantCoeff_zero hq)]

/-- **Negation `[-1]` has formal series `W.formalInverse`.** -/
@[simp]
theorem formalSeries_negIsogeny (W : WeierstrassCurve K) :
    (negIsogeny W.toAffine).formalSeries = W.formalInverse := by
  apply (formalSeries_eq_iff _ _).mpr
  have hw : (formalW W : K⸨X⸩) ≠ 0 := fun hw0 ↦
    (map_ne_zero W.functionFieldLaurentExpansion).mpr W.toAffine.genericY_ne_zero
      (by rw [W.functionFieldLaurentExpansion_genericY_eq_neg_one_div_formalW, hw0, div_zero])
  have hden_mul : (formalInverseDenom W : K⸨X⸩) *
      (PowerSeries.invOfUnit (formalInverseDenom W) 1 : K⸨X⸩) = 1 := by
    rw [← map_mul, mul_invOfUnit_formalInverseDenom, map_one]
  have hden0 : (formalInverseDenom W : K⸨X⸩) ≠ 0 := left_ne_zero_of_mul_eq_one hden_mul
  have hden : W.functionFieldLaurentExpansion
      ((W.toAffine⁄W.toAffine.FunctionField).toAffine.negY W.toAffine.genericX
        W.toAffine.genericY) =
        (formalInverseDenom W : K⸨X⸩) / (formalW W : K⸨X⸩) := by
    rw [eq_div_iff hw]
    simp only [Affine.negY, WeierstrassCurve.baseChange, map_a₁, map_a₃, map_sub, map_neg, map_mul,
      AlgHom.commutes, W.functionFieldLaurentExpansion_genericX_eq_X_div_formalW,
      W.functionFieldLaurentExpansion_genericY_eq_neg_one_div_formalW, formalInverseDenom_def,
      PowerSeries.coe_one, ← HahnSeries.algebraMap_apply', ← PowerSeries.algebraMap_eq,
      sub_mul, neg_mul, mul_assoc, div_mul_cancel₀ _ hw]
    dsimp only [WeierstrassCurve.toAffine]
    ring
  rw [map_div₀, map_neg, fieldPullback_negIsogeny_genericX, fieldPullback_negIsogeny_genericY,
    map_div₀, map_neg, hden, W.functionFieldLaurentExpansion_genericX_eq_X_div_formalW,
    formalInverse_def, PowerSeries.coe_neg, PowerSeries.coe_mul, eq_div_iff (div_ne_zero hden0 hw)]
  calc
    -(((PowerSeries.X : K⟦X⟧) : K⸨X⸩) * (PowerSeries.invOfUnit (formalInverseDenom W) 1 : K⸨X⸩)) *
        ((formalInverseDenom W : K⸨X⸩) / (formalW W : K⸨X⸩)) =
      -((PowerSeries.X : K⟦X⟧) * ((formalInverseDenom W : K⸨X⸩) *
        (PowerSeries.invOfUnit (formalInverseDenom W) 1 : K⸨X⸩))) / (formalW W : K⸨X⸩) := by ring
    _ = -((PowerSeries.X : K⟦X⟧) / (formalW W : K⸨X⸩)) := by rw [hden_mul, mul_one, neg_div]

namespace Hom

open scoped Classical in
/-- **The formal power series of a morphism**: `0` on the zero morphism, and `φ.formalSeries` on
an isogeny `φ`. -/
noncomputable def formalSeries (f : Hom W₁.toAffine W₂.toAffine) : K⟦X⟧ :=
  if hf : f = 0 then 0 else (toIsogeny hf).formalSeries

@[simp]
theorem formalSeries_zero : (0 : Hom W₁.toAffine W₂.toAffine).formalSeries = 0 :=
  dite_eq_left_of_eq_true (eq_true rfl)

@[simp]
theorem formalSeries_ofIsogeny (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ofIsogeny φ).formalSeries = φ.formalSeries := by
  rw [formalSeries, dite_eq_right_of_eq_false (eq_false (ofIsogeny_ne_zero φ)),
    toIsogeny_ofIsogeny]

/-- Every morphism's formal series has zero constant coefficient. -/
-- Handle composites, negatives, and multiples before `formalSeries_comp`, `formalSeries_neg`, or
-- `formalSeries_zsmul` rewrite them to substitutions.
@[simp↓]
theorem constantCoeff_formalSeries (f : Hom W₁.toAffine W₂.toAffine) :
    PowerSeries.constantCoeff f.formalSeries = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩ <;> simp

/-- A morphism vanishes if and only if its formal series vanishes. -/
@[simp]
theorem formalSeries_eq_zero_iff {f : Hom W₁.toAffine W₂.toAffine} :
    f.formalSeries = 0 ↔ f = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp
  · simp [φ.formalSeries_ne_zero, ofIsogeny_ne_zero φ]

/-- **A morphism is determined by its formal series.** -/
theorem formalSeries_injective :
    Function.Injective (formalSeries (W₁ := W₁) (W₂ := W₂)) := by
  intro f g h
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · exact (formalSeries_eq_zero_iff.mp (h.symm.trans formalSeries_zero)).symm
  rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
  · exact formalSeries_eq_zero_iff.mp (h.trans formalSeries_zero)
  · rw [formalSeries_ofIsogeny, formalSeries_ofIsogeny] at h
    exact congrArg ofIsogeny (Isogeny.formalSeries_injective h)

@[simp]
theorem formalSeries_inj {f g : Hom W₁.toAffine W₂.toAffine} :
    f.formalSeries = g.formalSeries ↔ f = g :=
  formalSeries_injective.eq_iff

/-- The identity morphism induces the identity formal series `X`. -/
@[simp]
theorem formalSeries_id (W : WeierstrassCurve K) :
    (Hom.id W.toAffine).formalSeries = PowerSeries.X := by
  rw [Hom.id_def, formalSeries_ofIsogeny, Isogeny.formalSeries_id]

/-- Composition of morphisms induces substitution of their formal series. -/
@[simp]
theorem formalSeries_comp (g : Hom W₂.toAffine W₃.toAffine) (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).formalSeries = PowerSeries.subst f.formalSeries g.formalSeries := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp [PowerSeries.subst_zero_of_constantCoeff_zero g.constantCoeff_formalSeries]
  rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
  · simp [PowerSeries.subst_zero]
  · simp

/-- **The formal series of `-f` is `W₂.formalInverse` composed with `f.formalSeries`.** -/
@[simp]
theorem formalSeries_neg (f : Hom W₁.toAffine W₂.toAffine) :
    (-f).formalSeries = PowerSeries.subst f.formalSeries W₂.formalInverse := by
  rw [neg_def, formalSeries_comp, formalSeries_ofIsogeny, formalSeries_negIsogeny]

section Add

variable [W₂.IsElliptic]

-- `Point.map` along `W₁.functionFieldLaurentExpansion : W₁.toAffine.FunctionField →ₐ[K] K⸨X⸩`
-- asks for `IsScalarTower K K K⸨X⸩` with `Algebra.toSMul`, whereas `HahnSeries` registers
-- `IsScalarTower` for its coefficientwise `SMul`.
private theorem instIsScalarTower_laurentSeries :
    @IsScalarTower K K K⸨X⸩ Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  .of_algebraMap_eq fun _ ↦ by
    simp only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply]

attribute [local instance] instIsScalarTower_laurentSeries

open scoped Classical in
/-- Evaluating along `W₁.functionFieldLaurentExpansion` in `K⸨X⸩` sends the tautological point of
`f` to `W₂.formalParamPoint f.formalSeries`. -/
private theorem point_map_tautologicalPoint_eq_formalParamPoint (f : Hom W₁.toAffine W₂.toAffine) :
    Point.map W₁.functionFieldLaurentExpansion f.tautologicalPoint =
      W₂.formalParamPoint (KK := K⸨X⸩) f.formalSeries := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · rw [tautologicalPoint_zero, map_zero, formalSeries_zero, formalParamPoint_zero]
  · have hid := (LaurentSeries.substAlgHom_eq_mvSubstAlgHom
      PowerSeries.constantCoeff_X PowerSeries.X_ne_zero).symm.trans
      (LaurentSeries.substAlgHom_X (K := K))
    have h := point_map_mvSubstAlgHom_tautologicalPoint (KK := K⸨X⸩) φ
      PowerSeries.constantCoeff_X PowerSeries.X_ne_zero
    rwa [hid, AlgHom.id_comp, PowerSeries.X_subst, ← tautologicalPoint_ofIsogeny,
      ← formalSeries_ofIsogeny] at h

open scoped Classical in
/-- **The formal series of a sum of morphisms is the formal-group sum of their series.** -/
theorem formalSeries_add (f g : Hom W₁.toAffine W₂.toAffine) :
    (f + g).formalSeries =
      subst ![f.formalSeries, g.formalSeries] (formalGroup W₂).toPowerSeries := by
  have hfc : PowerSeries.HasSubst f.formalSeries :=
    .of_constantCoeff_zero f.constantCoeff_formalSeries
  have hgc : PowerSeries.HasSubst g.formalSeries :=
    .of_constantCoeff_zero g.constantCoeff_formalSeries
  have hc : constantCoeff
      (subst ![f.formalSeries, g.formalSeries] (formalGroup W₂).toPowerSeries) = 0 :=
    constantCoeff_subst_eq_zero (hasSubst_finTwo hfc hgc)
      (fun i ↦ by fin_cases i; exacts [f.constantCoeff_formalSeries, g.constantCoeff_formalSeries])
      (formalGroup W₂).zero_constantCoeff
  refine (W₂.formalParamPoint_inj (KK := K⸨X⸩)
    (.of_constantCoeff_zero (f + g).constantCoeff_formalSeries)
    (.of_constantCoeff_zero hc)).mp ?_
  rw [← point_map_tautologicalPoint_eq_formalParamPoint, tautologicalPoint_add,
    (Point.map _).map_add, point_map_tautologicalPoint_eq_formalParamPoint,
    point_map_tautologicalPoint_eq_formalParamPoint,
    W₂.subst_formalGroup_toPowerSeries hfc hgc,
    W₂.formalParamPoint_subst_pair_formalAdd (KK := K⸨X⸩) hfc hgc]

/-- **The formal series of a difference of morphisms is the formal-group difference of their
series.** -/
theorem formalSeries_sub (f g : Hom W₁.toAffine W₂.toAffine) :
    (f - g).formalSeries =
      subst ![f.formalSeries, PowerSeries.subst g.formalSeries W₂.formalInverse]
        (formalGroup W₂).toPowerSeries := by
  rw [sub_eq_add_neg, formalSeries_add, formalSeries_neg]

/-- **`Hom.formalSeries` as an additive homomorphism into `(formalGroup W₂).Point Unit`.** -/
noncomputable def formalSeriesPointHom :
    Hom W₁.toAffine W₂.toAffine →+ (formalGroup W₂).Point Unit where
  toFun f := ⟨f.formalSeries, .of_constantCoeff_zero f.constantCoeff_formalSeries⟩
  map_zero' := Subtype.ext formalSeries_zero
  map_add' f g := Subtype.ext (formalSeries_add f g)

@[simp]
theorem val_formalSeriesPointHom (f : Hom W₁.toAffine W₂.toAffine) :
    (formalSeriesPointHom f).val = f.formalSeries := (rfl)

/-- `Hom.formalSeriesPointHom` is injective. -/
theorem formalSeriesPointHom_injective :
    Function.Injective (formalSeriesPointHom (W₁ := W₁) (W₂ := W₂)) :=
  fun _ _ h ↦ formalSeries_injective (congrArg Subtype.val h)

@[simp]
theorem formalSeriesPointHom_inj {f g : Hom W₁.toAffine W₂.toAffine} :
    formalSeriesPointHom f = formalSeriesPointHom g ↔ f = g :=
  formalSeriesPointHom_injective.eq_iff

/-- **The formal series of `n • f` (`n : ℕ`) is `[n]_{formalGroup W₂}` composed with
`f.formalSeries`.** -/
@[simp]
theorem formalSeries_nsmul (n : ℕ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalSeries = PowerSeries.subst f.formalSeries ((formalGroup W₂).nsmulSeries n) := by
  have h := congrArg Subtype.val (formalSeriesPointHom.map_nsmul n f)
  rwa [val_formalSeriesPointHom, ← (formalGroup W₂).subst_nsmulSeries (formalSeriesPointHom f) n,
    val_formalSeriesPointHom] at h

/-- **The formal series of `n • f` (`n : ℤ`) is `[n]_{formalGroup W₂}` composed with
`f.formalSeries`.** -/
@[simp]
theorem formalSeries_zsmul (n : ℤ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalSeries = PowerSeries.subst f.formalSeries ((formalGroup W₂).zsmulSeries n) := by
  have h := congrArg Subtype.val (formalSeriesPointHom.map_zsmul n f)
  rwa [val_formalSeriesPointHom, ← (formalGroup W₂).subst_zsmulSeries (formalSeriesPointHom f) n,
    val_formalSeriesPointHom] at h

end Add

/-- `Hom.formalSeriesPointHom` sends the identity morphism to the tautological point `X`. -/
@[simp]
theorem formalSeriesPointHom_id (W : WeierstrassCurve K) [W.IsElliptic] :
    formalSeriesPointHom (Hom.id W.toAffine) = (formalGroup W).tautologicalPoint := by
  apply Subtype.ext
  simp

end Hom

/-- **Multiplication by `n : ℤ` has formal series `(formalGroup W).zsmulSeries n`.** -/
@[simp]
theorem formalSeries_mulByIntIsogeny (W : WeierstrassCurve K) [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W.toAffine n ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalSeries = (formalGroup W).zsmulSeries n := by
  rw [← Hom.formalSeries_ofIsogeny, ofIsogeny_mulByIntIsogeny, Hom.formalSeries_zsmul,
    Hom.formalSeries_id, PowerSeries.X_subst]

/-- **Multiplication by `n : ℕ` has formal series `(formalGroup W).nsmulSeries n`.** -/
theorem formalSeries_mulByIntIsogeny_natCast (W : WeierstrassCurve K) [W.IsElliptic] {n : ℕ}
    (hn : psiFunctionField W.toAffine n ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalSeries = (formalGroup W).nsmulSeries n := by
  rw [formalSeries_mulByIntIsogeny, FormalGroup.zsmulSeries_natCast]

/-! ### Every isogeny and morphism induces a formal group homomorphism -/

section FormalGroupHom

open scoped Classical in
private theorem pointMap_map_algebraMap_formalParamPoint [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) {σ : Type*} {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0)
    {KK : Type*} [Field KK] [DecidableEq KK] [Algebra K KK] [Algebra (MvPowerSeries σ K) KK]
    [IsScalarTower K (MvPowerSeries σ K) KK] [IsFractionRing (MvPowerSeries σ K) KK] :
    ((Hom.ofIsogeny φ).map (algebraMap K KK)).pointMap (W₁.formalParamPoint (KK := KK) q) =
      W₂.formalParamPoint (KK := KK) (PowerSeries.subst q φ.formalSeries) := by
  have hid := point_map_mvSubstAlgHom_tautologicalPoint (KK := KK) (Isogeny.id W₁.toAffine) hq hq0
  rw [Isogeny.id_pullback, CoordinatePullback.tautologicalPoint_id, Isogeny.formalSeries_id,
    PowerSeries.subst_X (.of_constantCoeff_zero hq)] at hid
  refine (congrArg ((Hom.ofIsogeny φ).map (algebraMap K KK)).pointMap hid.symm).trans ?_
  refine (Hom.pointMap_map_algebraMap_map_genericPoint (Hom.ofIsogeny φ) _).trans ?_
  rw [Hom.tautologicalPoint_ofIsogeny]
  exact point_map_mvSubstAlgHom_tautologicalPoint (KK := KK) φ hq hq0

open scoped Classical in
/-- **Every isogeny's formal series satisfies the formal-group homomorphism equation**
`φ(F₁(X, Y)) = F₂(φ(X), φ(Y))`. -/
theorem subst_formalGroup_formalSeries [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    PowerSeries.subst (formalGroup W₁).toPowerSeries φ.formalSeries =
      subst (fun i ↦ φ.formalSeries.toMvPowerSeries i) (formalGroup W₂).toPowerSeries := by
  have := φ.isElliptic
  let KK := FractionRing (MvPowerSeries (Fin 2) K)
  have hX0 : (X 0 : MvPowerSeries (Fin 2) K) ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  have hX1 : (X 1 : MvPowerSeries (Fin 2) K) ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  have hF₁c : constantCoeff (formalGroup W₁).toPowerSeries = 0 :=
    (formalGroup W₁).zero_constantCoeff
  have hF₁0 : (formalGroup W₁).toPowerSeries ≠ 0 := fun h0 ↦
    zero_ne_one ((map_zero _).symm.trans (h0 ▸ (formalGroup W₁).lin_coeff_X))
  have hL : constantCoeff (PowerSeries.subst (formalGroup W₁).toPowerSeries φ.formalSeries) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hF₁c _ φ.constantCoeff_formalSeries
  set φ₀ : MvPowerSeries (Fin 2) K := PowerSeries.subst (X 0) φ.formalSeries
  set φ₁ : MvPowerSeries (Fin 2) K := PowerSeries.subst (X 1) φ.formalSeries
  have hφ0c : constantCoeff φ₀ = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X 0) _ φ.constantCoeff_formalSeries
  have hφ1c : constantCoeff φ₁ = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X 1) _ φ.constantCoeff_formalSeries
  have hpair : (fun i : Fin 2 ↦ φ.formalSeries.toMvPowerSeries i) = ![φ₀, φ₁] := by
    funext i; fin_cases i <;> simp [φ₀, φ₁, PowerSeries.toMvPowerSeries_eq_subst]
  rw [hpair]
  have hR : constantCoeff (subst ![φ₀, φ₁] (formalGroup W₂).toPowerSeries) = 0 :=
    constantCoeff_subst_eq_zero
      (hasSubst_finTwo (.of_constantCoeff_zero hφ0c) (.of_constantCoeff_zero hφ1c))
      (fun i ↦ by fin_cases i; exacts [hφ0c, hφ1c]) (formalGroup W₂).zero_constantCoeff
  refine (W₂.formalParamPoint_inj (KK := KK) (.of_constantCoeff_zero hL)
    (.of_constantCoeff_zero hR)).mp ?_
  have hF₁_self : (formalGroup W₁).toPowerSeries =
      subst ![X 0, X 1] (formalGroup W₁).toPowerSeries := by
    rw [finTwo_X_eq_X, subst_self, id_eq]
  have hadd₁ : W₁.formalParamPoint (KK := KK) (formalGroup W₁).toPowerSeries =
      W₁.formalParamPoint (KK := KK) (X (0 : Fin 2)) +
        W₁.formalParamPoint (KK := KK) (X (1 : Fin 2)) := by
    rw [hF₁_self, W₁.subst_formalGroup_toPowerSeries (PowerSeries.HasSubst.X _)
      (PowerSeries.HasSubst.X _), W₁.formalParamPoint_subst_pair_formalAdd
      (PowerSeries.HasSubst.X _) (PowerSeries.HasSubst.X _)]
  refine (pointMap_map_algebraMap_formalParamPoint (KK := KK) φ hF₁c hF₁0).symm.trans ?_
  refine (congrArg ((Hom.ofIsogeny φ).map (algebraMap K KK)).pointMap hadd₁).trans ?_
  refine (Hom.pointMap_add ((Hom.ofIsogeny φ).map (algebraMap K KK)) _ _).trans ?_
  rw [W₂.subst_formalGroup_toPowerSeries (.of_constantCoeff_zero hφ0c)
      (.of_constantCoeff_zero hφ1c),
    W₂.formalParamPoint_subst_pair_formalAdd (KK := KK) (.of_constantCoeff_zero hφ0c)
      (.of_constantCoeff_zero hφ1c)]
  exact congrArg₂ (· + ·)
    (pointMap_map_algebraMap_formalParamPoint (KK := KK) φ (constantCoeff_X (0 : Fin 2)) hX0)
    (pointMap_map_algebraMap_formalParamPoint (KK := KK) φ (constantCoeff_X (1 : Fin 2)) hX1)

/-- **The formal group homomorphism induced by an isogeny.** -/
noncomputable def formalGroupHom [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    FormalGroupHom (formalGroup W₁) (formalGroup W₂) where
  toPowerSeries := φ.formalSeries
  zero_constantCoeff := φ.constantCoeff_formalSeries
  hom := φ.subst_formalGroup_formalSeries

@[simp]
theorem formalGroupHom_toPowerSeries [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.formalGroupHom.toPowerSeries = φ.formalSeries := (rfl)

/-- `Isogeny.formalGroupHom` is injective. -/
theorem formalGroupHom_injective [W₂.IsElliptic] :
    Function.Injective (formalGroupHom (W₁ := W₁) (W₂ := W₂)) :=
  fun _ _ h ↦ formalSeries_injective (congrArg FormalGroupHom.toPowerSeries h)

@[simp]
theorem formalGroupHom_inj [W₂.IsElliptic] {φ ψ : Isogeny W₁.toAffine W₂.toAffine} :
    φ.formalGroupHom = ψ.formalGroupHom ↔ φ = ψ :=
  formalGroupHom_injective.eq_iff

/-- The identity isogeny induces the identity formal group homomorphism. -/
@[simp]
theorem formalGroupHom_id (W : WeierstrassCurve K) [W.IsElliptic] :
    (Isogeny.id W.toAffine).formalGroupHom = FormalGroupHom.id (formalGroup W) := by
  ext
  simp

/-- Composition of isogenies induces composition of formal group homomorphisms. -/
@[simp]
theorem formalGroupHom_comp [W₂.IsElliptic] [W₃.IsElliptic]
    (ψ : Isogeny W₂.toAffine W₃.toAffine) (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ψ.comp φ).formalGroupHom = ψ.formalGroupHom.comp φ.formalGroupHom := by
  ext
  simp

/-- Negation `[-1]` induces `(formalGroup W).zsmulHom (-1)` on the formal group. -/
@[simp]
theorem formalGroupHom_negIsogeny (W : WeierstrassCurve K) [W.IsElliptic] :
    (negIsogeny W.toAffine).formalGroupHom = (formalGroup W).zsmulHom (-1) := by
  ext
  simp [formalGroup_addInvX]

/-- Multiplication by `n : ℤ` induces `(formalGroup W).zsmulHom n` on the formal group. -/
@[simp]
theorem formalGroupHom_mulByIntIsogeny (W : WeierstrassCurve K) [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W.toAffine n ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalGroupHom = (formalGroup W).zsmulHom n := by
  ext
  simp

/-- Multiplication by `n : ℕ` induces `(formalGroup W).nsmulHom n` on the formal group. -/
theorem formalGroupHom_mulByIntIsogeny_natCast (W : WeierstrassCurve K) [W.IsElliptic] {n : ℕ}
    (hn : psiFunctionField W.toAffine n ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalGroupHom = (formalGroup W).nsmulHom n := by
  ext
  simp

/-- **The formal group homomorphism induced by an elliptic-curve morphism `Hom W₁ W₂`.** -/
noncomputable def Hom.formalGroupHom [W₂.IsElliptic] (f : Hom W₁.toAffine W₂.toAffine) :
    FormalGroupHom (formalGroup W₁) (formalGroup W₂) :=
  FormalGroupHom.ofHomDefectEqZero f.constantCoeff_formalSeries <| by
    rcases Hom.eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
    · simp
    · simpa using φ.formalGroupHom.homDefect_toPowerSeries

@[simp]
theorem Hom.formalGroupHom_toPowerSeries [W₂.IsElliptic] (f : Hom W₁.toAffine W₂.toAffine) :
    f.formalGroupHom.toPowerSeries = f.formalSeries :=
  FormalGroupHom.ofHomDefectEqZero_toPowerSeries _ _

/-- `Hom.formalGroupHom` is injective. -/
theorem Hom.formalGroupHom_injective [W₂.IsElliptic] :
    Function.Injective (Hom.formalGroupHom (W₁ := W₁) (W₂ := W₂)) :=
  fun _ _ h ↦ Hom.formalSeries_injective (by simpa using congrArg FormalGroupHom.toPowerSeries h)

@[simp]
theorem Hom.formalGroupHom_inj [W₂.IsElliptic] {f g : Hom W₁.toAffine W₂.toAffine} :
    f.formalGroupHom = g.formalGroupHom ↔ f = g :=
  Hom.formalGroupHom_injective.eq_iff

/-- On an isogeny, `Hom.formalGroupHom` agrees with `Isogeny.formalGroupHom`. -/
@[simp]
theorem Hom.formalGroupHom_ofIsogeny [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (Hom.ofIsogeny φ).formalGroupHom = φ.formalGroupHom := by
  ext
  simp

/-- The identity morphism induces the identity formal group homomorphism. -/
@[simp]
theorem Hom.formalGroupHom_id (W : WeierstrassCurve K) [W.IsElliptic] :
    (Hom.id W.toAffine).formalGroupHom = FormalGroupHom.id (formalGroup W) := by
  ext
  simp

/-- Composition of morphisms induces composition of formal group homomorphisms. -/
@[simp]
theorem Hom.formalGroupHom_comp [W₂.IsElliptic] [W₃.IsElliptic]
    (g : Hom W₂.toAffine W₃.toAffine) (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).formalGroupHom = g.formalGroupHom.comp f.formalGroupHom := by
  ext
  simp

/-- Negating a morphism composes its formal group homomorphism with `zsmulHom (-1)`. -/
@[simp]
theorem Hom.formalGroupHom_neg [W₂.IsElliptic] (f : Hom W₁.toAffine W₂.toAffine) :
    (-f).formalGroupHom = ((formalGroup W₂).zsmulHom (-1)).comp f.formalGroupHom := by
  rw [Hom.neg_def, Hom.formalGroupHom_comp, Hom.formalGroupHom_ofIsogeny,
    formalGroupHom_negIsogeny]

/-- Natural scalar multiplication on `Hom` composes with `(formalGroup W₂).nsmulHom n`. -/
@[simp]
theorem Hom.formalGroupHom_nsmul [W₂.IsElliptic] (n : ℕ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalGroupHom = ((formalGroup W₂).nsmulHom n).comp f.formalGroupHom := by
  ext
  simp

/-- Integer scalar multiplication on `Hom` composes with `(formalGroup W₂).zsmulHom n`. -/
@[simp]
theorem Hom.formalGroupHom_zsmul [W₂.IsElliptic] (n : ℤ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalGroupHom = ((formalGroup W₂).zsmulHom n).comp f.formalGroupHom := by
  ext
  simp

/-- The zero morphism acts as `0` on formal-group points. -/
@[simp]
theorem Hom.formalGroupHom_zero_applyPoint [W₂.IsElliptic] {σ : Type*}
    (x : (formalGroup W₁).Point σ) :
    (0 : Hom W₁.toAffine W₂.toAffine).formalGroupHom.applyPoint x = 0 := by
  apply Subtype.ext
  simp [PowerSeries.subst_zero]

/-- A sum of morphisms acts on formal-group points by the formal-group sum of their images. -/
@[simp]
theorem Hom.formalGroupHom_add_applyPoint [W₂.IsElliptic] (f g : Hom W₁.toAffine W₂.toAffine)
    {σ : Type*} (x : (formalGroup W₁).Point σ) :
    (f + g).formalGroupHom.applyPoint x =
      f.formalGroupHom.applyPoint x + g.formalGroupHom.applyPoint x := by
  apply Subtype.ext
  have hfg : HasSubst ![f.formalSeries, g.formalSeries] :=
    hasSubst_finTwo (.of_constantCoeff_zero f.constantCoeff_formalSeries)
      (.of_constantCoeff_zero g.constantCoeff_formalSeries)
  simp only [FormalGroupHom.applyPoint_val, Hom.formalGroupHom_toPowerSeries,
    Hom.formalSeries_add, FormalGroup.add_apply, PowerSeries.subst_def,
    subst_comp_subst_apply hfg x.prop.const]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The negation of a morphism acts on formal-group points by negating the image. -/
theorem Hom.formalGroupHom_neg_applyPoint [W₂.IsElliptic] (f : Hom W₁.toAffine W₂.toAffine)
    {σ : Type*} (x : (formalGroup W₁).Point σ) :
    (-f).formalGroupHom.applyPoint x = -(f.formalGroupHom.applyPoint x) := by
  simp

/-- A difference of morphisms acts on formal-group points by the difference of their images. -/
@[simp]
theorem Hom.formalGroupHom_sub_applyPoint [W₂.IsElliptic] (f g : Hom W₁.toAffine W₂.toAffine)
    {σ : Type*} (x : (formalGroup W₁).Point σ) :
    (f - g).formalGroupHom.applyPoint x =
      f.formalGroupHom.applyPoint x - g.formalGroupHom.applyPoint x := by
  rw [sub_eq_add_neg, Hom.formalGroupHom_add_applyPoint, Hom.formalGroupHom_neg_applyPoint,
    sub_eq_add_neg]

/-- An integer multiple `n • f` acts on formal-group points by `n • f(x)`. -/
theorem Hom.formalGroupHom_zsmul_applyPoint [W₂.IsElliptic] (n : ℤ)
    (f : Hom W₁.toAffine W₂.toAffine) {σ : Type*} (x : (formalGroup W₁).Point σ) :
    (n • f).formalGroupHom.applyPoint x = n • f.formalGroupHom.applyPoint x := by
  simp

/-- A natural multiple `n • f` acts on formal-group points by `n • f(x)`. -/
theorem Hom.formalGroupHom_nsmul_applyPoint [W₂.IsElliptic] (n : ℕ)
    (f : Hom W₁.toAffine W₂.toAffine) {σ : Type*} (x : (formalGroup W₁).Point σ) :
    (n • f).formalGroupHom.applyPoint x = n • f.formalGroupHom.applyPoint x := by
  simp

end FormalGroupHom

end Isogeny

end TauCeti

end
