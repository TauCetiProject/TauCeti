/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.GroupPairing
import Mathlib.Tactic.Group

/-!
# Pairing identities for line bundle classes satisfying the parallelogram law

Let `G` be a commutative group object of `Over S` and `c : LineBundleClass G.left` a line bundle
class on `G` satisfying the parallelogram law (`LineBundleClass.ParallelogramLaw c`). This file
derives the symmetry and power laws of its pairing `LineBundleClass.pairing c x y` and the
quadratic scaling of pullbacks along power endomorphisms of `G`.

## Main results

* `TauCeti.AlgebraicGeometry.LineBundleClass.pairing_comm`: on a commutative monoid object, the
  pairing is symmetric in its two `T`-points.
* `TauCeti.AlgebraicGeometry.LineBundleClass.ParallelogramLaw.pairing_mul_mul_pairing_div`:
  `⟨x * y, z⟩_c · ⟨x / y, z⟩_c = ⟨x, z⟩_c ^ 2`.
* `TauCeti.AlgebraicGeometry.LineBundleClass.ParallelogramLaw.pairing_pow_left`:
  `⟨x ^ m, y⟩_c = ⟨x, y⟩_c ^ m`.
* `TauCeti.AlgebraicGeometry.LineBundleClass.ParallelogramLaw.pow_pairing_eq_pairing_pow`:
  `⟨x, y⟩_{c ^ m} = ⟨x ^ m, y⟩_c`.
* `TauCeti.AlgebraicGeometry.LineBundleClass.ParallelogramLaw.pullback_pow_id`: if `c` is
  rigidified along the unit section (`1^* c = 1`), then `(𝟙 G ^ m)^* c = c ^ (m ^ 2)`.

## Provenance

Adapted from `New.Variety.pairing_comm`, `New.Pic.ParallelogramLaw.pairing_add_add_pairing_sub`,
`New.Pic.ParallelogramLaw.pairing_nsmul_left`,
`New.Pic.ParallelogramLaw.nsmul_pairing_eq_pairing_nsmul`, and `New.Variety.pull_nsmul_eq_sq_smul`
in `src/Lib/Shimura/AbelianScheme/Pairings.lean` of `grh-lean`
(https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
Apache 2.0, Copyright 2026 Anthropic, PBC), translated to Mathlib's multiplicative
`LineBundleClass` and `CategoryTheory.MonObj` / `CategoryTheory.GrpObj` conventions.
-/

public section

open CategoryTheory MonObj

open scoped CategoryTheory.MonObj

namespace TauCeti.AlgebraicGeometry.LineBundleClass

universe u

variable {S : AlgebraicGeometry.Scheme.{u}} {G : Over S}

/-- On a commutative monoid object `G` over `S`, the pairing of a line bundle class is symmetric
in its two `T`-points. -/
theorem pairing_comm [MonObj G] [IsCommMonObj G] (c : LineBundleClass G.left) {T : Over S}
    (x y : T ⟶ G) : pairing c x y = pairing c y x := by
  simp only [pairing_def, mul_comm x y]
  ac_rfl

namespace ParallelogramLaw

variable [GrpObj G] [IsCommMonObj G] {c : LineBundleClass G.left}

/-- If `c` satisfies the parallelogram law on a commutative group object `G`, its pairing obeys
`⟨x * y, z⟩_c · ⟨x / y, z⟩_c = ⟨x, z⟩_c ^ 2` for all `T`-points `x`, `y`, `z`. -/
theorem pairing_mul_mul_pairing_div (hc : ParallelogramLaw c) {T : Over S} (x y z : T ⟶ G) :
    pairing c (x * y) z * pairing c (x / y) z = pairing c x z ^ 2 := by
  have h1 := (parallelogramLaw_iff c).mp hc T (x * z) y
  have h2 := (parallelogramLaw_iff c).mp hc T x y
  rw [show x * z * y = x * y * z by ac_rfl,
    show x * z / y = x / y * z by rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]] at h1
  have h12 := congrArg₂ (· * ·) h1 (congrArg Inv.inv h2)
  have hmul :
      pullback (x * y * z).left c * pullback (x / y * z).left c *
        (pullback (x * y).left c * pullback (x / y).left c)⁻¹ =
      pullback (x * z).left c ^ 2 * (pullback x.left c ^ 2)⁻¹ := by
    have hL :
        pullback (x * y * z).left c * pullback (x / y * z).left c *
            pullback (1 : T ⟶ G).left c ^ 2 *
          (pullback (x * y).left c * pullback (x / y).left c *
            pullback (1 : T ⟶ G).left c ^ 2)⁻¹ =
        pullback (x * y * z).left c * pullback (x / y * z).left c *
          (pullback (x * y).left c * pullback (x / y).left c)⁻¹ := by
      simp only [mul_inv]; rw [show ∀ a b d e : LineBundleClass T.left,
        a * b * d * (e * d⁻¹) = a * b * e * (d * d⁻¹) by intro a b d e; ac_rfl,
        mul_inv_cancel, _root_.mul_one]
    have hR :
        (pullback (x * z).left c * pullback y.left c) ^ 2 *
          ((pullback x.left c * pullback y.left c) ^ 2)⁻¹ =
        pullback (x * z).left c ^ 2 * (pullback x.left c ^ 2)⁻¹ := by
      simp only [mul_pow, mul_inv]; rw [show ∀ a b d : LineBundleClass T.left,
        a * b * (d * b⁻¹) = a * d * (b * b⁻¹) by intro a b d; ac_rfl,
        mul_inv_cancel, _root_.mul_one]
    exact hL.symm.trans (h12.trans hR)
  have hscale := congrArg (· * ((pullback z.left c)⁻¹ * pullback (1 : T ⟶ G).left c) ^ 2) hmul
  simp only [sq, mul_inv] at hscale
  simp only [pairing_def, sq]
  have hL2 (a b d e f g : LineBundleClass T.left) :
      a * d * f * g * (b * e * f * g) = a * b * (d * e) * (f * g * (f * g)) := by ac_rfl
  have hR2 (a b d e : LineBundleClass T.left) :
      a * a * (b * b) * (d * e * (d * e)) = a * b * d * e * (a * b * d * e) := by ac_rfl
  exact (hL2 _ _ _ _ _ _).trans (hscale.trans (hR2 _ _ _ _))

/-- If `c` satisfies the parallelogram law on a commutative group object `G`, then
`⟨x ^ m, y⟩_c = ⟨x, y⟩_c ^ m` for every natural number `m`. -/
theorem pairing_pow_left (hc : ParallelogramLaw c) {T : Over S} (x y : T ⟶ G) (m : ℕ) :
    pairing c (x ^ m) y = pairing c x y ^ m := by
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more m ih ih' =>
    have hstep : pairing c (x ^ (m + 2)) y * pairing c (x ^ m) y =
        pairing c (x ^ (m + 1)) y ^ 2 := by
      have h := hc.pairing_mul_mul_pairing_div (x ^ (m + 1)) x y
      rwa [← pow_succ, show x ^ (m + 1) / x = x ^ m by rw [pow_succ, mul_div_cancel_right]] at h
    rw [ih, ih'] at hstep
    apply mul_right_cancel (b := pairing c x y ^ m)
    rw [hstep, ← pow_mul, ← pow_add]
    congr 1
    omega

/-- If `c` satisfies the parallelogram law on a commutative group object `G`, then the pairing of
`c ^ m` at `(x, y)` equals the pairing of `c` at `(x ^ m, y)`. -/
theorem pow_pairing_eq_pairing_pow (hc : ParallelogramLaw c) {T : Over S} (x y : T ⟶ G) (m : ℕ) :
    pairing (c ^ m) x y = pairing c (x ^ m) y := by
  rw [hc.pairing_pow_left]
  induction m with
  | zero => simp
  | succ m ih => simp [pow_succ, ih]

/-- If `c` satisfies the parallelogram law on a commutative group object `G` and is rigidified
along the unit section (`1^* c = 1`), then pulling `c` back along the `m`-th power endomorphism
of `G` yields `c ^ (m ^ 2)`. -/
theorem pullback_pow_id (hc : ParallelogramLaw c) (h1 : pullback (1 : G ⟶ G).left c = 1) (m : ℕ) :
    pullback ((𝟙 G : G ⟶ G) ^ m).left c = c ^ (m ^ 2) := by
  induction m with
  | zero => simpa using h1
  | succ m ih =>
    have htwo : pullback ((𝟙 G : G ⟶ G) * 𝟙 G).left c = c ^ 4 := by
      have h := (parallelogramLaw_iff c).mp hc G (𝟙 G) (𝟙 G)
      simp only [div_self', h1, one_pow, _root_.mul_one, Over.id_left, pullback_id] at h
      simpa [show (c * c) ^ 2 = c ^ 4 by rw [← sq, ← pow_mul]] using h
    have hpair := hc.pairing_pow_left (𝟙 G) (𝟙 G) m
    simp only [pairing_def, ← pow_succ, h1, htwo, Over.id_left, pullback_id, _root_.mul_one,
      ih] at hpair
    have hrhs : c ^ 4 * c⁻¹ * c⁻¹ = c ^ 2 := by group
    rw [hrhs, ← pow_mul] at hpair
    apply mul_right_cancel (b := (c ^ (m ^ 2))⁻¹ * c⁻¹)
    rw [← _root_.mul_assoc, hpair, ← mul_inv, eq_mul_inv_iff_mul_eq, ← _root_.mul_assoc,
      ← pow_add, ← pow_succ]
    congr 1
    ring

end ParallelogramLaw

end TauCeti.AlgebraicGeometry.LineBundleClass
