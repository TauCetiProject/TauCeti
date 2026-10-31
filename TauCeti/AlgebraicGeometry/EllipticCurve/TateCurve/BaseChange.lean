/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Parameter
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Specialization
public import Mathlib.Analysis.Normed.Module.Basic
import TauCeti.Algebra.Algebra.Hom
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

For `q ∈ Kˣ` and `K`-algebras `L` and `M`, a `K`-algebra map `ι : L → M` acts on parameters
through `tateParameterMap q ι : Lˣ / q^ℤ → Mˣ / q^ℤ`. Unlike `tateParameterBaseChange f q`, whose
target is the quotient by `f q`, it lands in the quotient by the image of `q ∈ K` in `M`. So for
`M = L` it is an endomorphism of `Lˣ / q^ℤ`, and the automorphisms of `L/K` act on a single group.

## Main definitions

* `TauCeti.tateParameterBaseChange`: the map `Kˣ / q^ℤ → Lˣ / f(q)^ℤ` induced by a ring
  homomorphism.
* `TauCeti.tateParameterMap`: the map `Lˣ / q^ℤ → Mˣ / q^ℤ` induced by a `K`-algebra map.

## Main results

* `TauCeti.map_tateCurveAt`: specialization of the formal Tate equation commutes with the
  embedding.
* `TauCeti.map_tateUniformizationX` and `TauCeti.map_tateUniformizationY`: the analytic Tate
  coordinates commute with the embedding.
* `TauCeti.tateQuotientCoordinates_tateParameterBaseChange`: the descended coordinate pair is
  compatible with base change.
* `TauCeti.tateQuotientCoordinates_tateParameterMap`: the descended coordinate pair commutes with
  continuous `K`-algebra maps.
* `TauCeti.baseChange_tateCurveAt`: the base change of `E_q` to a normed `K`-algebra `L` is the
  Tate curve of the image of `q`.

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

section ParameterMaps

variable [CommRing K] [CommRing L] {M N : Type*} [CommRing M] [CommRing N]
  [Algebra K L] [Algebra K M] [Algebra K N]

/-- The map `Lˣ / q^ℤ → Mˣ / q^ℤ` induced by a `K`-algebra map `ι : L → M`, for `q ∈ Kˣ`. It is
`tateParameterBaseChange ι` for the image of `q` in `L`, with its target identified along
`AlgHom.units_map_units_map_algebraMap`. -/
noncomputable def tateParameterMap (q : Kˣ) (ι : L →ₐ[K] M) :
    Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q) →*
      Mˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K M : K →* M) q) :=
  (QuotientGroup.quotientMulEquivOfEq
    (congrArg Subgroup.zpowers (ι.units_map_units_map_algebraMap q))).toMonoidHom.comp
    (tateParameterBaseChange (ι : L →+* M) _)

/-- The parameter map sends the class of a unit to the class of its image. -/
@[simp]
theorem tateParameterMap_mk (q : Kˣ) (ι : L →ₐ[K] M) (u : Lˣ) :
    tateParameterMap q ι (u : Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q)) =
      (Units.map (ι : L →* M) u :
        Mˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K M : K →* M) q)) := by
  rw [tateParameterMap, MonoidHom.comp_apply, tateParameterBaseChange_mk, MulEquiv.coe_toMonoidHom,
    QuotientGroup.quotientMulEquivOfEq_mk]
  -- the sides differ only in coercing `ι` to a monoid hom directly or through `L →+* M`
  rfl

/-- The identity map acts trivially on parameters. -/
@[simp]
theorem tateParameterMap_id (q : Kˣ) :
    tateParameterMap q (AlgHom.id K L) = MonoidHom.id _ := by
  ext u
  simpa using congrArg _ (Units.ext (by simp))

/-- The parameter map is functorial. -/
theorem tateParameterMap_comp (q : Kˣ) (ι : L →ₐ[K] M) (κ : M →ₐ[K] N) :
    tateParameterMap q (κ.comp ι) = (tateParameterMap q κ).comp (tateParameterMap q ι) := by
  ext u
  simpa using congrArg _ (Units.ext (by simp))

/-- The parameter map is compatible with base change from `K`. -/
@[simp]
theorem tateParameterMap_tateParameterBaseChange (q : Kˣ) (ι : L →ₐ[K] M)
    (x : Kˣ ⧸ Subgroup.zpowers q) :
    tateParameterMap q ι (tateParameterBaseChange (algebraMap K L) q x) =
      tateParameterBaseChange (algebraMap K M) q x := by
  induction x using QuotientGroup.induction_on with
  | H u => simpa using congrArg _ (Units.ext (by simp))

/-- An injective `K`-algebra map induces an injective map on parameters. -/
theorem tateParameterMap_injective (q : Kˣ) {ι : L →ₐ[K] M} (hι : Function.Injective ι) :
    Function.Injective (tateParameterMap q ι) :=
  (QuotientGroup.quotientMulEquivOfEq
    (congrArg Subgroup.zpowers (ι.units_map_units_map_algebraMap q))).injective.comp
    (tateParameterBaseChange_injective (ι : L →+* M) hι _)

end ParameterMaps

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

section Extension

open WeierstrassCurve

variable [NormedField K] [NormedField L] [NormedAlgebra K L]

/-- The Tate coordinates on parameters commute with a continuous `K`-algebra map. -/
theorem tateQuotientCoordinates_tateParameterMap [CompleteSpace L] [IsUltrametricDist L]
    {M : Type*} [NormedField M] [NormedAlgebra K M] (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (ι : L →ₐ[K] M) (hι : Continuous ι)
    (x : Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q)) :
    tateQuotientCoordinates _ (tateParameterMap q ι x) =
      (ι (tateQuotientCoordinates _ x).1, ι (tateQuotientCoordinates _ x).2) := by
  induction x using QuotientGroup.induction_on with
  | H u =>
    have h := tateQuotientCoordinates_tateParameterBaseChange (ι : L →+* M) hι _
      (by simpa using hq) (u : Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q))
    rw [tateParameterBaseChange_mk, ι.units_map_units_map_algebraMap] at h
    exact h

variable (L) in
/-- **The base change of the Tate curve is the Tate curve of the image of `q`.** -/
theorem baseChange_tateCurveAt [CompleteSpace K] [IsUltrametricDist K] [CompleteSpace L]
    [IsUltrametricDist L] (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    (tateCurveAt q hq)⁄L =
      tateCurveAt (Units.map (algebraMap K L : K →* L) q) (by simpa using hq) :=
  haveI : RingHomIsometric (algebraMap K L) := ⟨norm_algebraMap' L _⟩
  map_tateCurveAt (algebraMap K L) q hq

end Extension

end TauCeti

end
