/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.TautologicalPoint

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

## Main results

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

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

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
