/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Units.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace.Polynomial
public import TauCeti.KnotTheory.Hecke.Trace
public import TauCeti.RingTheory.AdjoinRoot.Basic

/-!
# Quadratic coefficient extension for normalized Hecke braid traces

For the Ocneanu Markov trace with unit parameter `a : Rˣ` on the infinite type-A Hecke algebra at
`q : Rˣ`, the positive and negative stabilization constants are `a` and `a - (q - q⁻¹)`. When the
negative stabilization constant is also a unit `b : Rˣ`, normalizing `MarkovBraid.heckeTrace`
requires a writhe unit `l` satisfying `l ^ 2 = b * a⁻¹` together with the strand-number factor
`C = (l * a)⁻¹`. Such a square root need not exist in `R`.

Adjoining a root of the monic quadratic polynomial `X ^ 2 - C (b * a⁻¹)` produces the universal
commutative `R`-algebra `AdjoinRoot (X ^ 2 - C (b * a⁻¹))` carrying that unit root
(`TauCeti.heckeRootUnit`). Over any commutative ring `R`, the Ocneanu trace factor of any braid
comes from the base ring `R` (`TauCeti.MarkovBraid.heckeQuadraticTrace_eq_mul_algebraMap`), the
trace satisfies the unknot, unlink, strand-inclusion, and skein identities, and when
`b = a - (q - q⁻¹)` it descends to unframed Markov equivalence
(`TauCeti.heckeQuadraticBraidInvariant`). Any `R`-algebra carrying a chosen unit root receives this
universal invariant via `AdjoinRoot.algHomEquiv`
(`TauCeti.MarkovBraid.algHomEquiv_symm_heckeQuadraticTrace` and
`TauCeti.algHomEquiv_symm_heckeQuadraticBraidInvariant`).

## Main definitions

* `TauCeti.heckeRootUnit`: the canonical unit square root of `b * a⁻¹` in
  `AdjoinRoot (X ^ 2 - C (b * a⁻¹))`.
* `TauCeti.MarkovBraid.heckeQuadraticTrace`: the normalized Ocneanu braid trace in the universal
  quadratic root extension.
* `TauCeti.heckeQuadraticBraidInvariant`: its descent to `Quot MarkovEquiv`.

## Main results

* `TauCeti.MarkovBraid.heckeQuadraticTrace_one`,
  `TauCeti.MarkovBraid.heckeQuadraticTrace_one_strand`,
  `TauCeti.MarkovBraid.heckeQuadraticTrace_strandIncl`, and
  `TauCeti.MarkovBraid.heckeQuadraticTrace_skein`: characteristic normalization and skein laws of
  `heckeQuadraticTrace`.
* `TauCeti.MarkovBraid.heckeQuadraticTrace_eq_mul_algebraMap`: the Ocneanu trace factor comes from
  the base ring `R`, while only the writhe and strand-count prefactors lie in the extension.
* `TauCeti.MarkovBraid.algHomEquiv_symm_heckeQuadraticTrace` and
  `TauCeti.algHomEquiv_symm_heckeQuadraticBraidInvariant`: specializing along any `R`-algebra choice
  of unit square root recovers the normalized Ocneanu braid trace and invariant in that algebra.

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

/-- When `b = a - (q - q⁻¹)`, `heckeRootUnit a b` satisfies the quadratic stabilization relation
`l ^ 2 * a = a - (q - q⁻¹)` in `AdjoinRoot (X ^ 2 - C (b * a⁻¹))`. -/
theorem heckeRootUnit_sq_mul (q a b : Rˣ) (hb : (b : R) = (a : R) - ((q : R) - ↑q⁻¹)) :
    (heckeRootUnit a b : AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))) ^ 2 *
        algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))) a =
      algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))) a -
        (Units.val (Units.map
            (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom q) -
          Units.val (Units.map
            (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom q)⁻¹) := by
  have hba : ((b * a⁻¹ : Rˣ) : R) * a = (a : R) - ((q : R) - ↑q⁻¹) := by
    rw [Units.val_mul, mul_assoc, Units.inv_mul, mul_one, hb]
  rw [heckeRootUnit_sq, ← map_mul, hba]
  simp

namespace MarkovBraid

/-- The normalized Ocneanu braid trace at parameter `a`, valued in the universal quadratic root
extension `AdjoinRoot (X ^ 2 - C (b * a⁻¹))`. -/
def heckeQuadraticTrace (β : MarkovBraid) (q a b : Rˣ) :
    AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)) :=
  let S := AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))
  let ι : R →+* S := algebraMap R S
  let q' : Sˣ := Units.map ι.toMonoidHom q
  let a' : Sˣ := Units.map ι.toMonoidHom a
  let l : Sˣ := heckeRootUnit a b
  β.heckeTrace (ocneanuTrace S q' (ι a)) (Units.val (l * a')⁻¹) l

/-- Unfolding formula for `MarkovBraid.heckeQuadraticTrace`. -/
theorem heckeQuadraticTrace_def (β : MarkovBraid) (q a b : Rˣ) :
    β.heckeQuadraticTrace q a b =
      β.heckeTrace
        (ocneanuTrace (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))
          (Units.map (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom q)
          (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))) a))
        (Units.val (heckeRootUnit a b *
          Units.map (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom a)⁻¹)
        (heckeRootUnit a b) := (rfl)

/-- On the `(n + 1)`-strand identity braid, `heckeQuadraticTrace` equals `((l * a)⁻¹) ^ n`. -/
@[simp]
theorem heckeQuadraticTrace_one (q a b : Rˣ) (n : ℕ) :
    heckeQuadraticTrace ⟨n, 1⟩ q a b =
      Units.val (heckeRootUnit a b *
        Units.map (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom a)⁻¹ ^
        n := by
  rw [heckeQuadraticTrace_def, heckeTrace_one (isMarkovTrace_ocneanuTrace _).map_one]

/-- On a one-strand braid, `heckeQuadraticTrace` is `1`. -/
@[simp]
theorem heckeQuadraticTrace_one_strand (q a b : Rˣ) (c : BraidGroup 1) :
    heckeQuadraticTrace ⟨0, c⟩ q a b = 1 := by
  rw [heckeQuadraticTrace_def, heckeTrace_one_strand (isMarkovTrace_ocneanuTrace _).map_one]

/-- Adding an uncrossed strand multiplies `heckeQuadraticTrace` by `(l * a)⁻¹`. -/
@[simp]
theorem heckeQuadraticTrace_strandIncl (q a b : Rˣ) {n : ℕ} (c : BraidGroup (n + 1)) :
    heckeQuadraticTrace ⟨n + 1, BraidGroup.strandIncl c⟩ q a b =
      Units.val (heckeRootUnit a b *
        Units.map (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom a)⁻¹ *
        heckeQuadraticTrace ⟨n, c⟩ q a b := by
  rw [heckeQuadraticTrace_def, heckeQuadraticTrace_def, LinearMap.heckeTrace_strandIncl]

/-- Skein relation of `heckeQuadraticTrace` in `AdjoinRoot (X ^ 2 - C (b * a⁻¹))`. -/
theorem heckeQuadraticTrace_skein (q a b : Rˣ) {n : ℕ} (c d : BraidGroup (n + 1)) (i : Fin n) :
    (↑(heckeRootUnit a b)⁻¹ : AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))) *
          heckeQuadraticTrace ⟨n, c * BraidGroup.sigma (n := n + 1) i * d⟩ q a b -
        (heckeRootUnit a b : AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))) *
          heckeQuadraticTrace ⟨n, c * (BraidGroup.sigma (n := n + 1) i)⁻¹ * d⟩ q a b =
      algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))) ((q : R) - ↑q⁻¹) *
        heckeQuadraticTrace ⟨n, c * d⟩ q a b := by
  have hq : algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))) ((q : R) - ↑q⁻¹) =
      Units.val (Units.map
          (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom q) -
        Units.val (Units.map
          (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom q)⁻¹ := by
    simp
  rw [heckeQuadraticTrace_def, heckeQuadraticTrace_def, heckeQuadraticTrace_def, hq]
  exact heckeTrace_skein _ (heckeRootUnit a b) c d i

/-- In `heckeQuadraticTrace`, the Ocneanu trace factor is the image under `algebraMap R` of the
base-ring Ocneanu trace, while only the normalization prefactor uses the adjoined root. -/
theorem heckeQuadraticTrace_eq_mul_algebraMap (β : MarkovBraid) (q a b : Rˣ) :
    β.heckeQuadraticTrace q a b =
      Units.val (heckeRootUnit a b *
          Units.map (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom a)⁻¹ ^
          β.predStrands *
        Units.val (heckeRootUnit a b ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid)) *
          algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))
            (ocneanuTrace R q a (braidHom R q (β.predStrands + 1) β.braid)) := by
  have hq : algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))) q =
      Units.val (Units.map
        (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom q) := by
    simp
  rw [heckeQuadraticTrace_def, heckeTrace_def, ocneanuTrace_braidHom_algebraMap hq]

/-- **Universal property of `heckeQuadraticTrace`.** Given any commutative `R`-algebra `S` and any
unit `l : Sˣ` satisfying `l ^ 2 = algebraMap R S (b * a⁻¹)`, the induced `R`-algebra homomorphism
maps `β.heckeQuadraticTrace q a b` to the normalized Ocneanu braid trace in `S`. -/
theorem algHomEquiv_symm_heckeQuadraticTrace {S : Type*} [CommRing S] [Algebra R S]
    (β : MarkovBraid) (q a b : Rˣ) {q' : Sˣ} (hq : algebraMap R S q = q')
    (l : Sˣ) (hl : (l : S) ^ 2 = algebraMap R S ((b * a⁻¹ : Rˣ) : R)) :
    (AdjoinRoot.algHomEquiv S (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))).symm
        ⟨(l : S), by simp [hl]⟩ (β.heckeQuadraticTrace q a b) =
      β.heckeTrace (ocneanuTrace S q' (algebraMap R S a))
        (Units.val (l * Units.map (algebraMap R S).toMonoidHom a)⁻¹) l := by
  set φ : AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)) →ₐ[R] S :=
    (AdjoinRoot.algHomEquiv S (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))).symm ⟨(l : S), by simp [hl]⟩
  have hφl : Units.map φ.toRingHom.toMonoidHom (heckeRootUnit a b) = l := by
    ext
    simp [φ, coe_heckeRootUnit]
  have hφa : Units.map φ.toRingHom.toMonoidHom
      (Units.map (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom a) =
      Units.map (algebraMap R S).toMonoidHom a :=
    Units.ext <| by simpa using φ.commutes (a : R)
  have hφinv : φ (Units.val (heckeRootUnit a b *
      Units.map (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom a)⁻¹) =
      Units.val (l * Units.map (algebraMap R S).toMonoidHom a)⁻¹ := by
    have hmul : Units.map φ.toRingHom.toMonoidHom
        ((heckeRootUnit a b *
          Units.map (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom a)⁻¹) =
        (l * Units.map (algebraMap R S).toMonoidHom a)⁻¹ := by
      rw [_root_.map_inv, _root_.map_mul, hφl, hφa]
    simpa using congrArg Units.val hmul
  have hφzpow (e : ℤ) : φ (Units.val (heckeRootUnit a b ^ e)) = Units.val (l ^ e) := by
    have hzpow : Units.map φ.toRingHom.toMonoidHom (heckeRootUnit a b ^ e) = l ^ e := by
      rw [_root_.map_zpow (Units.map φ.toRingHom.toMonoidHom), hφl]
    have h := congrArg Units.val hzpow
    rw [Units.coe_map] at h
    simpa using h
  rw [heckeQuadraticTrace_eq_mul_algebraMap, heckeTrace_def, map_mul, map_mul, map_pow, hφinv,
    hφzpow, AlgHom.commutes, ocneanuTrace_braidHom_algebraMap hq]

end MarkovBraid

/-- Markov-equivalent braids have equal `heckeQuadraticTrace` when `b = a - (q - q⁻¹)`. -/
theorem MarkovEquiv.heckeQuadraticTrace_eq {β γ : MarkovBraid} (h : MarkovEquiv β γ)
    (q a b : Rˣ) (hb : (b : R) = (a : R) - ((q : R) - ↑q⁻¹)) :
    β.heckeQuadraticTrace q a b = γ.heckeQuadraticTrace q a b :=
  h.heckeTrace_eq_of_sq_mul (isMarkovTrace_ocneanuTrace _)
    (Units.map (algebraMap R (AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)))).toMonoidHom a)
    (heckeRootUnit a b) (by simp) (heckeRootUnit_sq_mul q a b hb)

/-- The normalized Ocneanu braid invariant on `Quot MarkovEquiv` valued in the universal quadratic
extension `AdjoinRoot (X ^ 2 - C (b * a⁻¹))`. -/
def heckeQuadraticBraidInvariant (q a b : Rˣ) (hb : (b : R) = (a : R) - ((q : R) - ↑q⁻¹)) :
    Quot MarkovEquiv → AdjoinRoot (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R)) :=
  Quot.lift (fun β ↦ β.heckeQuadraticTrace q a b)
    (fun _ _ h ↦ h.heckeQuadraticTrace_eq q a b hb)

/-- Evaluation of `heckeQuadraticBraidInvariant` on a braid representative. -/
@[simp]
theorem heckeQuadraticBraidInvariant_mk (q a b : Rˣ) (hb : (b : R) = (a : R) - ((q : R) - ↑q⁻¹))
    (β : MarkovBraid) :
    heckeQuadraticBraidInvariant q a b hb (Quot.mk MarkovEquiv β) =
      β.heckeQuadraticTrace q a b := (rfl)

/-- **Universal property of `heckeQuadraticBraidInvariant`.** Specializing along any commutative
`R`-algebra `S` with a unit `l : Sˣ` satisfying `l ^ 2 = algebraMap R S (b * a⁻¹)` recovers
`heckeBraidInvariant` of the Ocneanu trace in `S`. -/
theorem algHomEquiv_symm_heckeQuadraticBraidInvariant {S : Type*} [CommRing S] [Algebra R S]
    (q a b : Rˣ) (hb : (b : R) = (a : R) - ((q : R) - ↑q⁻¹))
    {q' : Sˣ} (hq : algebraMap R S q = q')
    (l : Sˣ) (hl : (l : S) ^ 2 = algebraMap R S ((b * a⁻¹ : Rˣ) : R))
    (x : Quot MarkovEquiv) :
    (AdjoinRoot.algHomEquiv S (X ^ 2 - C ((b * a⁻¹ : Rˣ) : R))).symm
        ⟨(l : S), by simp [hl]⟩ (heckeQuadraticBraidInvariant q a b hb x) =
      heckeBraidInvariant (isMarkovTrace_ocneanuTrace (R := S) (q := q') (algebraMap R S a))
        (Units.val (l * Units.map (algebraMap R S).toMonoidHom a)⁻¹) l
        (Units.val_inv_mul_mul_mul_eq_one (Units.map (algebraMap R S).toMonoidHom a) l (by simp))
        (Units.val_inv_mul_mul_inv_mul_eq_one (z := algebraMap R S a)
          (Units.map (algebraMap R S).toMonoidHom a) l (by simp)
          (by
            have hba : ((b * a⁻¹ : Rˣ) : R) * a = (a : R) - ((q : R) - ↑q⁻¹) := by
              rw [Units.val_mul, mul_assoc, Units.inv_mul, mul_one, hb]
            have hq' : Units.map (algebraMap R S).toMonoidHom q = q' :=
              Units.ext (by simpa using hq)
            have hqinv : algebraMap R S ↑q⁻¹ = ↑q'⁻¹ := by
              rw [← hq']
              simp
            rw [hl, ← map_mul, hba, map_sub, map_sub, hq, hqinv]))
        x := by
  induction x using Quot.ind with
  | _ β =>
    rw [heckeQuadraticBraidInvariant_mk, heckeBraidInvariant_mk]
    exact β.algHomEquiv_symm_heckeQuadraticTrace q a b hq l hl

end TauCeti
