/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace
public import TauCeti.KnotTheory.Hecke.Trace
public import TauCeti.RingTheory.AdjoinRoot.Basic

/-!
# Quadratic coefficient extension for normalized Hecke braid traces

For a Markov trace with parameter `z` on the infinite type-A Hecke algebra at `q : Rˣ`, the
positive and negative stabilization constants are `z` and `z - (q - q⁻¹)`. When both constants
are units `a, b : Rˣ`, normalizing `MarkovBraid.heckeTrace` requires a writhe unit `l` satisfying
`l ^ 2 = b * a⁻¹` together with the strand-number factor `C = (l * a)⁻¹`. Such a square root need
not exist in `R`.

Adjoining a root of the monic quadratic polynomial `X ^ 2 - C (b * a⁻¹)` produces the universal
commutative `R`-algebra `AdjoinRoot (X ^ 2 - C (b * a⁻¹))` carrying that unit root
(`TauCeti.heckeRootUnit`). Over any commutative ring `R`, `R` embeds faithfully into this free
rank-two `R`-algebra (`TauCeti.algebraMap_adjoinRoot_hecke_injective`), the Ocneanu trace of any
braid lies in the image of `R`, and the normalized braid trace descends to unframed Markov
equivalence (`TauCeti.heckeQuadraticBraidInvariant`). Any `R`-algebra carrying a chosen unit root
receives this universal invariant by `AdjoinRoot.algHomEquiv`
(`TauCeti.MarkovBraid.algHom_heckeQuadraticTrace`).

## Main definitions

* `TauCeti.heckeRootUnit`: the canonical unit square root of `b * a⁻¹` in
  `AdjoinRoot (X ^ 2 - C (b * a⁻¹))`.
* `TauCeti.MarkovBraid.heckeQuadraticTrace`: the normalized Ocneanu braid trace in the universal
  quadratic root extension.
* `TauCeti.heckeQuadraticBraidInvariant`: its descent to `Quot MarkovEquiv`.

## Main results

* `TauCeti.algebraMap_adjoinRoot_hecke_injective`: `algebraMap R` into the quadratic extension is
  injective over any commutative ring.
* `TauCeti.MarkovBraid.heckeQuadraticTrace_eq_mul_algebraMap`: the Ocneanu trace factor comes from
  the base ring `R`, while only the writhe and strand-count prefactors lie in the extension.
* `TauCeti.MarkovBraid.algHom_heckeQuadraticTrace`: specializing along any `R`-algebra choice of
  unit square root recovers the normalized Ocneanu braid trace in that algebra.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Section 6.
* C. Kassel and V. Turaev, *Braid Groups*, Springer GTM 247 (2008), Section 4.2.
-/

public noncomputable section

namespace TauCeti

open Polynomial InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R]

/-- The canonical unit square root of `b * a⁻¹` in the quadratic `R`-algebra
`AdjoinRoot (X ^ 2 - C (b * a⁻¹))`. -/
def heckeRootUnit (a b : Rˣ) :
    (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))ˣ :=
  (AdjoinRoot.isUnit_root_X_pow_sub_C (b * a⁻¹).isUnit two_ne_zero).unit

/-- The underlying element of `heckeRootUnit a b` is `AdjoinRoot.root`. -/
@[simp]
theorem coe_heckeRootUnit (a b : Rˣ) :
    (heckeRootUnit a b : AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))) =
      AdjoinRoot.root (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)) :=
  IsUnit.unit_spec _

/-- The square of `heckeRootUnit a b` is the image of `b * a⁻¹`. -/
theorem heckeRootUnit_sq (a b : Rˣ) :
    (heckeRootUnit a b : AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))) ^ 2 =
      algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))) ((b * a⁻¹ : Rˣ) : R) := by
  rw [coe_heckeRootUnit, AdjoinRoot.root_X_pow_sub_C_pow, AdjoinRoot.algebraMap_eq]

/-- Over every commutative ring `R`, the base ring injects into the quadratic extension
`AdjoinRoot (X ^ 2 - C (b * a⁻¹))`. -/
theorem algebraMap_adjoinRoot_hecke_injective (a b : Rˣ) :
    Function.Injective (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Function.injective_of_subsingleton _
  · rw [AdjoinRoot.algebraMap_eq]
    refine AdjoinRoot.of.injective_of_monic_of_degree_pos
      (monic_X_pow_sub_C _ two_ne_zero) ?_
    rw [degree_X_pow_sub_C zero_lt_two]
    exact Nat.cast_pos.mpr zero_lt_two

/-- When `a = z` and `b = z - (q - q⁻¹)`, `heckeRootUnit a b` satisfies the quadratic
stabilization relation `l ^ 2 * z = z - (q - q⁻¹)` in `AdjoinRoot (X ^ 2 - C (b * a⁻¹))`. -/
theorem heckeRootUnit_sq_mul (q a b : Rˣ) {z : R} (ha : (a : R) = z)
    (hb : (b : R) = z - ((q : R) - ↑q⁻¹)) :
    (heckeRootUnit a b : AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))) ^ 2 *
        algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))) z =
      algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))) z -
        (Units.val (Units.map
            (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom q) -
          Units.val (Units.map
            (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom q)⁻¹) := by
  have hba : ((b * a⁻¹ : Rˣ) : R) * z = z - ((q : R) - ↑q⁻¹) := by
    rw [← ha, Units.val_mul, mul_assoc, Units.inv_mul, mul_one, ha, hb]
  have hqinv :
      Units.val (Units.map
          (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom q)⁻¹ =
        algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))) ↑q⁻¹ := by
    rw [← _root_.map_inv]
    rfl
  rw [heckeRootUnit_sq, ← map_mul, hba, map_sub, map_sub, hqinv]
  rfl

namespace MarkovBraid

/-- The normalized Ocneanu braid trace valued in the universal quadratic root extension
`AdjoinRoot (X ^ 2 - C (b * a⁻¹))`. -/
def heckeQuadraticTrace (β : MarkovBraid) (q a b : Rˣ) (z : R) :
    AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)) :=
  let S := AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))
  let ι : R →+* S := algebraMap R S
  let q' : Sˣ := Units.map ι.toMonoidHom q
  let a' : Sˣ := Units.map ι.toMonoidHom a
  let l : Sˣ := heckeRootUnit a b
  β.heckeTrace (ocneanuTrace S q' (ι z)) (Units.val (l * a')⁻¹) l

/-- Unfolding formula for `MarkovBraid.heckeQuadraticTrace`. -/
theorem heckeQuadraticTrace_def (β : MarkovBraid) (q a b : Rˣ) (z : R) :
    β.heckeQuadraticTrace q a b z =
      β.heckeTrace
        (ocneanuTrace (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))
          (Units.map (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom q)
          (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))) z))
        (Units.val (heckeRootUnit a b *
          Units.map (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom a)⁻¹)
        (heckeRootUnit a b) := (rfl)

/-- In `heckeQuadraticTrace`, the Ocneanu trace factor is the image under `algebraMap R` of the
base-ring Ocneanu trace, while only the normalization prefactor uses the adjoined root. -/
theorem heckeQuadraticTrace_eq_mul_algebraMap (β : MarkovBraid) (q a b : Rˣ) (z : R) :
    β.heckeQuadraticTrace q a b z =
      Units.val (heckeRootUnit a b *
          Units.map (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom a)⁻¹ ^
          β.predStrands *
        Units.val (heckeRootUnit a b ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid)) *
          algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))
            (ocneanuTrace R q z (braidHom R q (β.predStrands + 1) β.braid)) := by
  rw [heckeQuadraticTrace_def, heckeTrace_def, ocneanuTrace_braidHom_algebraMap rfl]

/-- **Universal property of `heckeQuadraticTrace`.** Given any commutative `R`-algebra `S` and any
unit `l : Sˣ` satisfying `l ^ 2 = algebraMap R S (b * a⁻¹)`, the induced `R`-algebra homomorphism
maps `β.heckeQuadraticTrace q a b z` to the normalized Ocneanu braid trace in `S`. -/
theorem algHom_heckeQuadraticTrace {S : Type*} [CommRing S] [Algebra R S]
    (β : MarkovBraid) (q a b : Rˣ) (z : R) {q' : Sˣ} (hq : algebraMap R S q = q')
    (l : Sˣ) (hl : (l : S) ^ 2 = algebraMap R S ((b * a⁻¹ : Rˣ) : R)) :
    (AdjoinRoot.algHomEquiv S (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))).symm
        ⟨(l : S), by simp [hl]⟩ (β.heckeQuadraticTrace q a b z) =
      β.heckeTrace (ocneanuTrace S q' (algebraMap R S z))
        (Units.val (l * Units.map (algebraMap R S).toMonoidHom a)⁻¹) l := by
  set φ : AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)) →ₐ[R] S :=
    (AdjoinRoot.algHomEquiv S (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))).symm ⟨(l : S), by simp [hl]⟩
  have hφl : Units.map φ.toRingHom.toMonoidHom (heckeRootUnit a b) = l := by
    ext
    simp [φ, coe_heckeRootUnit]
  have hφa : Units.map φ.toRingHom.toMonoidHom
      (Units.map (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom a) =
      Units.map (algebraMap R S).toMonoidHom a :=
    Units.ext (φ.commutes (a : R))
  have hφinv : φ (Units.val (heckeRootUnit a b *
      Units.map (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom a)⁻¹) =
      Units.val (l * Units.map (algebraMap R S).toMonoidHom a)⁻¹ := by
    have hmul : Units.map φ.toRingHom.toMonoidHom
        ((heckeRootUnit a b *
          Units.map (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom a)⁻¹) =
        (l * Units.map (algebraMap R S).toMonoidHom a)⁻¹ := by
      rw [_root_.map_inv, _root_.map_mul, hφl, hφa]
    exact congrArg Units.val hmul
  have hφzpow (e : ℤ) : φ (Units.val (heckeRootUnit a b ^ e)) = Units.val (l ^ e) := by
    have hzpow : Units.map φ.toRingHom.toMonoidHom (heckeRootUnit a b ^ e) = l ^ e := by
      rw [_root_.map_zpow (Units.map φ.toRingHom.toMonoidHom), hφl]
    exact congrArg Units.val hzpow
  rw [heckeQuadraticTrace_eq_mul_algebraMap, heckeTrace_def, map_mul, map_mul, map_pow, hφinv,
    hφzpow, AlgHom.commutes, ocneanuTrace_braidHom_algebraMap hq]

end MarkovBraid

/-- Markov-equivalent braids have equal `heckeQuadraticTrace` when `a = z` and
`b = z - (q - q⁻¹)`. -/
theorem MarkovEquiv.heckeQuadraticTrace_eq {β γ : MarkovBraid} (h : MarkovEquiv β γ)
    (q a b : Rˣ) {z : R} (ha : (a : R) = z) (hb : (b : R) = z - ((q : R) - ↑q⁻¹)) :
    β.heckeQuadraticTrace q a b z = γ.heckeQuadraticTrace q a b z :=
  h.heckeTrace_eq_of_sq_mul (isMarkovTrace_ocneanuTrace _)
    (Units.map (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom a)
    (heckeRootUnit a b) (by simp [ha]) (heckeRootUnit_sq_mul q a b ha hb)

/-- The normalized Ocneanu braid invariant on `Quot MarkovEquiv` valued in the universal quadratic
extension `AdjoinRoot (X ^ 2 - C (b * a⁻¹))`. -/
def heckeQuadraticBraidInvariant (q a b : Rˣ) {z : R} (ha : (a : R) = z)
    (hb : (b : R) = z - ((q : R) - ↑q⁻¹)) :
    Quot MarkovEquiv → AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)) :=
  Quot.lift (fun β ↦ β.heckeQuadraticTrace q a b z)
    (fun _ _ h ↦ h.heckeQuadraticTrace_eq q a b ha hb)

/-- Evaluation of `heckeQuadraticBraidInvariant` on a braid representative. -/
@[simp]
theorem heckeQuadraticBraidInvariant_mk (q a b : Rˣ) {z : R} (ha : (a : R) = z)
    (hb : (b : R) = z - ((q : R) - ↑q⁻¹)) (β : MarkovBraid) :
    heckeQuadraticBraidInvariant q a b ha hb (Quot.mk MarkovEquiv β) =
      β.heckeQuadraticTrace q a b z := (rfl)

end TauCeti
