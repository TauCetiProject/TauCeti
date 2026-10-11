/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing.LaurentExpansion
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Chart
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.FormalPoint
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Eval

/-!
# Global functions on the projective Weierstrass model

Let `W` be a Weierstrass curve over a commutative ring `R`. This file shows that the only global
functions on the projective Weierstrass model `E = projModel W` are the constants: the structure
morphism `E ⟶ Spec R` induces an isomorphism `R ≅ Γ(E, 𝒪_E)`
(`WeierstrassCurve.isIso_appTop_projModelOver`). No hypothesis on `W` or on `R` is needed; in
particular `W` need not be elliptic and `R` need not be reduced.

The proof restricts a global function `h` to the **tautological point** `[x : y : 1]` of `E`, with
values in the affine coordinate ring `R[W] = R[x, y] ⧸ (W(x, y))`
(`WeierstrassCurve.tautologicalPoint`). This gives a function `g ∈ R[W]` on the affine curve.
Through the Laurent expansion `R[W] → R⸨z⸩` at the point at infinity
(`WeierstrassCurve.laurentExpansion`), the tautological point becomes the formal point
`[z : -1 : w(z)]` along the zero section, which has values in the power series ring `R⟦z⟧`
(`WeierstrassCurve.SpecMap_laurentExpansion_tautologicalPoint`). So the Laurent expansion of `g`
is the power series obtained by restricting `h` to the formal point: `g` has no pole at infinity,
and is therefore a constant. Finally the tautological point restricts to the chart `D₊(Z)`, which
is scheme-theoretically dense in `E`, so `h` is determined by `g`.

## Main definitions

* `WeierstrassCurve.tautologicalPoint W`: the point `[x : y : 1]` of `projModel W` with values in
  the affine coordinate ring `R[W]`.

## Main results

* `WeierstrassCurve.exists_SpecMap_comp_tautologicalPoint_eq_chartι`: the chart `D₊(Z)` factors
  through the tautological point.
* `WeierstrassCurve.SpecMap_laurentExpansion_tautologicalPoint`: expanded at the point at
  infinity, the tautological point is the formal point.
* `WeierstrassCurve.isIso_appTop_projModelOver`: the global functions on the projective
  Weierstrass model are the constants.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.5.8 and IV.1.
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1–2.2.
-/

public section

open CategoryTheory AlgebraicGeometry PowerSeries LaurentSeries

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] {W : WeierstrassCurve R}

/-- The coordinate functions `(x, y, 1)` over the affine coordinate ring `R[W]` solve the
homogeneous Weierstrass equation of `W`. -/
theorem equation_tautologicalPoint :
    (W.toProjective.map (algebraMap R W.toAffine.CoordinateRing)).Equation
      ![AdjoinRoot.of W.toAffine.polynomial Polynomial.X, AdjoinRoot.root W.toAffine.polynomial,
        1] :=
  (Projective.equation_some _ _).mpr (Affine.CoordinateRing.equation_X_root W.toAffine)

variable (W)

/-- The **tautological point** `[x : y : 1]` of the projective Weierstrass model, with values in
the affine coordinate ring `R[W] = R[x, y] ⧸ (W(x, y))`. Rewrite with `tautologicalPoint_def`
rather than unfolding this definition. -/
noncomputable def tautologicalPoint : Spec (.of W.toAffine.CoordinateRing) ⟶ W.projModel :=
  W.projModelPoint (algebraMap R _) equation_tautologicalPoint (i := 2) (by simp)

/-- The tautological point is the point of the projective model with homogeneous coordinates
`(x, y, 1)`, along `algebraMap R R[W]`. -/
theorem tautologicalPoint_def : W.tautologicalPoint =
    W.projModelPoint (algebraMap R _) equation_tautologicalPoint (i := 2) (by simp) := (rfl)

/-- The tautological point lies over the morphism `Spec R[W] ⟶ Spec R` induced by
`algebraMap R R[W]`. -/
@[reassoc (attr := simp)]
theorem tautologicalPoint_projModelOver : W.tautologicalPoint ≫ W.projModelOver =
    Spec.map (CommRingCat.ofHom (algebraMap R W.toAffine.CoordinateRing)) := by
  rw [tautologicalPoint_def, projModelPoint_projModelOver]

/-- The chart `D₊(Z)` of the projective model factors through the tautological point: the
universal point of the chart is `[X / Z : Y / Z : 1]`, the image of `[x : y : 1]` under an
`R`-algebra map `R[W] → ChartRing 2`. -/
theorem exists_SpecMap_comp_tautologicalPoint_eq_chartι :
    ∃ k : W.toAffine.CoordinateRing →ₐ[R] W.toProjective.ChartRing 2,
      Spec.map (CommRingCat.ofHom k.toRingHom) ≫ W.tautologicalPoint = W.chartι 2 := by
  -- the universal point of the chart is `(X / Z, Y / Z, 1)`
  have hP : W.toProjective.chartPoint 2 = ![W.toProjective.chartPoint 2 0,
      W.toProjective.chartPoint 2 1, 1] := funext fun k ↦ by
    fin_cases k <;> simp
  have hE := W.toProjective.equation_chartPoint 2
  rw [hP] at hE
  refine ⟨Affine.CoordinateRing.evalAlgHom ((Projective.equation_some _ _).mp hE), ?_⟩
  rw [tautologicalPoint_def, SpecMap_projModelPoint, chartι_eq_projModelPoint,
    projModelPoint_eq_projModelPoint_iff]
  refine ⟨RingHom.ext (Affine.CoordinateRing.evalAlgHom _).commutes, 1, funext fun k ↦ ?_⟩
  fin_cases k <;> simp

/-- **The tautological point at infinity.** Expanded in Laurent series at the point at infinity,
the tautological point `[x : y : 1]` is the formal point `[z : -1 : w(z)]`: its coordinates are
`-y` times those of the formal point. -/
theorem SpecMap_laurentExpansion_tautologicalPoint :
    Spec.map (CommRingCat.ofHom (W.laurentExpansion : W.toAffine.CoordinateRing →+* R⸨X⸩)) ≫
        W.tautologicalPoint =
      Spec.map (CommRingCat.ofHom (HahnSeries.ofPowerSeries ℤ R)) ≫ W.projModelFormalPoint := by
  have hy := W.laurentExpansion_root_mul_formalW
  have hx := W.laurentExpansion_of_X_eq_neg_X_mul_laurentExpansion_root
  rw [tautologicalPoint_def, projModelFormalPoint_def, SpecMap_projModelPoint,
    SpecMap_projModelPoint, projModelPoint_eq_projModelPoint_iff]
  refine ⟨(W.laurentExpansion.comp_algebraMap).trans rfl,
    (IsUnit.of_mul_eq_one (HahnSeries.ofPowerSeries ℤ R (formalW W))
      (by rw [neg_mul, hy, neg_neg])).unit, funext fun k ↦ ?_⟩
  fin_cases k
  · simp [-laurentExpansion_of_X, -laurentExpansion_root, Units.smul_def, hx]
    ring
  · simp [Units.smul_def]
  · simp [-laurentExpansion_root, Units.smul_def, hy]

/-- **The global functions on the projective Weierstrass model are the constants.** The structure
morphism `projModel W ⟶ Spec R` induces an isomorphism `Γ(Spec R, ⊤) ≅ Γ(projModel W, ⊤)`, for
every Weierstrass curve `W` over every commutative ring `R`. -/
instance isIso_appTop_projModelOver : IsIso W.projModelOver.appTop := by
  -- `res h ∈ R[W]` is the restriction of a global function `h` to the tautological point
  let res (h : Γ(W.projModel, ⊤)) : W.toAffine.CoordinateRing :=
    (Scheme.ΓSpecIso _).hom (W.tautologicalPoint.appTop h)
  -- it restricts constants to constants
  have hπ (a : Γ(Spec (.of R), ⊤)) :
      res (W.projModelOver.appTop a) = algebraMap R _ ((Scheme.ΓSpecIso _).hom a) := by
    have := congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
      (algebraMap R W.toAffine.CoordinateRing))) a)
    rw [← tautologicalPoint_projModelOver, Scheme.Hom.comp_appTop] at this
    simpa using this
  -- the Laurent expansion of `res h` is the restriction of `h` to the formal point
  have hL (h : Γ(W.projModel, ⊤)) : W.laurentExpansion (res h) =
      HahnSeries.ofPowerSeries ℤ R ((Scheme.ΓSpecIso _).hom (W.projModelFormalPoint.appTop h)) := by
    have hcat : W.tautologicalPoint.appTop ≫ (Scheme.ΓSpecIso _).hom ≫
        CommRingCat.ofHom (W.laurentExpansion : W.toAffine.CoordinateRing →+* R⸨X⸩) =
        W.projModelFormalPoint.appTop ≫ (Scheme.ΓSpecIso _).hom ≫
          CommRingCat.ofHom (HahnSeries.ofPowerSeries ℤ R) := by
      rw [← Scheme.ΓSpecIso_naturality, ← Scheme.ΓSpecIso_naturality, ← Category.assoc,
        ← Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.Hom.comp_appTop,
        SpecMap_laurentExpansion_tautologicalPoint]
    simpa using congr($hcat h)
  -- a global function is determined by its restriction to the dense chart `D₊(Z)`
  have hres : Function.Injective res := by
    obtain ⟨k, hk⟩ := W.exists_SpecMap_comp_tautologicalPoint_eq_chartι
    have h2 : Function.Injective (W.chartι 2).appTop := (W.chartι 2).app_injective ⊤
    rw [← hk, Scheme.Hom.comp_appTop, ConcreteCategory.coe_comp] at h2
    exact (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.injective.comp h2.of_comp
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun a b hab ↦ ?_, fun h ↦ ?_⟩
  · have := (hπ a).symm.trans ((congrArg res hab).trans (hπ b))
    exact (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.injective
      (FaithfulSMul.algebraMap_injective R _ this)
  · -- `res h` has no pole at infinity, so it is a constant `β`
    obtain ⟨β, hβ⟩ := W.exists_eq_algebraMap_of_coeff_laurentExpansion_eq_zero_of_neg
      (g := res h) fun m hm ↦ by simp [hL, PowerSeries.coeff_coe, hm]
    exact ⟨(Scheme.ΓSpecIso _).inv β, hres <| by simpa [hπ] using hβ.symm⟩

end WeierstrassCurve
