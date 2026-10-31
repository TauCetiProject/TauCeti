/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Parameter
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Specialization
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Base change of Tate curves and their parameters

The analytic Tate equation commutes with isometric homomorphisms of complete non-archimedean
normed rings, and its two coordinate series commute with continuous homomorphisms of normed
fields. Consequently the multiplicative parameter map descends from units to the quotients by
`q^ℤ`, and the descended coordinate pair is compatible with that map.

These comparisons are the extension-compatibility input for the point-level Tate uniformisation.
They apply in particular to finite extensions equipped with their norm-preserving field embedding.

## Main definitions

* `TauCeti.tateParameterBaseChange`: the map `Kˣ / q^ℤ → Lˣ / f(q)^ℤ` induced by a ring
  homomorphism.

## Main results

* `TauCeti.map_tateCurveAt`: specialization of the formal Tate equation commutes with the
  embedding.
* `TauCeti.map_tateUniformizationX` and `TauCeti.map_tateUniformizationY`: the analytic Tate
  coordinates commute with the embedding.
* `TauCeti.tateQuotientCoordinates_tateParameterBaseChange`: the descended coordinate pair is
  compatible with base change.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.3.
* J. Tate, *A review of non-Archimedean elliptic functions* (1995).
-/

public section

open PowerSeries

namespace TauCeti

variable {K L : Type*}

section Coefficients

variable [NormedCommRing K] [CompleteSpace K] [IsUltrametricDist K]
  [NormedCommRing L] [CompleteSpace L] [IsUltrametricDist L]
  (f : K →+* L) [RingHomIsometric f]

/-- The fourth analytic Tate coefficient commutes with an isometric ring homomorphism. -/
theorem map_tateCurveA₄ (q : K) (hq : ‖q‖ < 1) :
    f (tateCurveA₄ q hq) =
      tateCurveA₄ (f q) (by rwa [RingHomIsometric.norm_map]) := by
  rw [tateCurveA₄_eq, tateCurveA₄_eq, map_mul, map_neg,
    map_divisorSumAt f (RingHom.isometry f).continuous 3 q hq]
  simp only [map_ofNat]

/-- The sixth analytic Tate coefficient commutes with an isometric ring homomorphism. -/
theorem map_tateCurveA₆ (q : K) (hq : ‖q‖ < 1) :
    f (tateCurveA₆ q hq) =
      tateCurveA₆ (f q) (by rwa [RingHomIsometric.norm_map]) := by
  rw [tateCurveA₆_def, tateCurveA₆_def,
    Summable.map_tsum (summable_intCast_mul_pow (fun n ↦ coeff n tateCurve.a₆) hq) f
      (RingHom.isometry f).continuous]
  apply tsum_congr
  intro n
  simp

/-- The specialized Tate equation commutes with an isometric ring homomorphism. -/
theorem map_tateCurveAt (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    (tateCurveAt q hq).map f =
      tateCurveAt (Units.map f q) (by simpa using hq) := by
  apply WeierstrassCurve.ext
  · rw [WeierstrassCurve.map_a₁, tateCurveAt_a₁, map_one, tateCurveAt_a₁]
  · rw [WeierstrassCurve.map_a₂, tateCurveAt_a₂, map_zero, tateCurveAt_a₂]
  · rw [WeierstrassCurve.map_a₃, tateCurveAt_a₃, map_zero, tateCurveAt_a₃]
  · simp only [WeierstrassCurve.map_a₄, tateCurveAt_a₄]
    convert map_tateCurveA₄ f (q : K) hq using 1
    all_goals simp
  · simp only [WeierstrassCurve.map_a₆, tateCurveAt_a₆]
    convert map_tateCurveA₆ f (q : K) hq using 1
    all_goals simp

end Coefficients

section Coordinates

variable [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [NormedField L]
  (f : K →+* L) (hf : Continuous f)
include hf

/-- The first analytic Tate coordinate commutes with a continuous field homomorphism. -/
theorem map_tateUniformizationX (q u : Kˣ) (hq : ‖(q : K)‖ < 1) :
    f (tateUniformizationX q u) =
      tateUniformizationX (Units.map f q) (Units.map f u) := by
  rw [tateUniformizationX_def, tateUniformizationX_def, map_sub, map_mul,
    map_divisorSumAt f hf 1 (q : K) hq,
    Summable.map_tsum (summable_tateUniformizationX q hq u) f hf]
  simp only [map_ofNat, Units.coe_map]
  congr 1
  apply tsum_congr
  intro n
  simp

/-- The second analytic Tate coordinate commutes with a continuous field homomorphism. -/
theorem map_tateUniformizationY (q u : Kˣ) (hq : ‖(q : K)‖ < 1) :
    f (tateUniformizationY q u) =
      tateUniformizationY (Units.map f q) (Units.map f u) := by
  rw [tateUniformizationY_def, tateUniformizationY_def, map_add,
    map_divisorSumAt f hf 1 (q : K) hq,
    Summable.map_tsum (summable_tateUniformizationY q hq u) f hf]
  congr 1
  apply tsum_congr
  intro n
  simp

end Coordinates

section Parameters

variable [CommRing K] [CommRing L] (f : K →+* L)

/-- Base change of multiplicative Tate parameters, from `Kˣ / q^ℤ` to `Lˣ / f(q)^ℤ`. -/
noncomputable def tateParameterBaseChange (q : Kˣ) :
    Kˣ ⧸ Subgroup.zpowers q →* Lˣ ⧸ Subgroup.zpowers (Units.map (f : K →* L) q) :=
  QuotientGroup.map (Subgroup.zpowers q) (Subgroup.zpowers (Units.map (f : K →* L) q))
    (Units.map (f : K →* L))
    (Subgroup.map_le_iff_le_comap.mp (MonoidHom.map_zpowers _ q).le)

/-- Base change of Tate parameters sends the class of a unit to the class of its image. -/
@[simp]
theorem tateParameterBaseChange_mk (q u : Kˣ) :
    tateParameterBaseChange f q (u : Kˣ ⧸ Subgroup.zpowers q) =
      (Units.map (f : K →* L) u :
        Lˣ ⧸ Subgroup.zpowers (Units.map (f : K →* L) q)) := by
  apply QuotientGroup.map_mk

/-- An injective coefficient map induces an injective map on Tate parameters. -/
theorem tateParameterBaseChange_injective (hf : Function.Injective f) (q : Kˣ) :
    Function.Injective (tateParameterBaseChange f q) := by
  apply (injective_iff_map_eq_one (tateParameterBaseChange f q)).mpr
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H u =>
    rw [tateParameterBaseChange_mk, QuotientGroup.eq_one_iff] at hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    apply (QuotientGroup.eq_one_iff u).mpr
    refine Subgroup.mem_zpowers_iff.mpr
      ⟨n, Units.map_injective (f := (f : K →* L)) hf ?_⟩
    simpa only [map_zpow] using hn

end Parameters

section ParameterCoordinates

variable [NormedField K] [NormedField L] (f : K →+* L)

/-- The coordinate pair on the multiplicative quotient commutes with continuous base change. -/
theorem tateQuotientCoordinates_tateParameterBaseChange [CompleteSpace K] [IsUltrametricDist K]
    (hf : Continuous f) (q : Kˣ) (hq : ‖(q : K)‖ < 1) (x : Kˣ ⧸ Subgroup.zpowers q) :
    tateQuotientCoordinates (Units.map (f : K →* L) q) (tateParameterBaseChange f q x) =
      (f (tateQuotientCoordinates q x).1, f (tateQuotientCoordinates q x).2) := by
  induction x using QuotientGroup.induction_on with
  | H u =>
    rw [tateParameterBaseChange_mk, tateQuotientCoordinates_mk,
      tateQuotientCoordinates_mk, map_tateUniformizationX f hf q u hq,
      map_tateUniformizationY f hf q u hq]

end ParameterCoordinates

end TauCeti

end
