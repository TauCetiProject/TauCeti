/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Half-skew and polarization identities for bilinear maps

For an alternating bilinear map `ω` with `2` invertible, halving `ω` gives a bilinear map whose
skew part `⅟2 • ω - (⅟2 • ω)ᵀ` recovers `ω` itself (`LinearMap.IsAlt.invOf_two_smul_sub_flip`).

For a general bilinear map `B` with `2` invertible, half of its skew part `ω = B - Bᵀ` and its
quadratic diagonal `q x = ⅟2 • B x x` satisfy the coboundary relation
`⅟2 • ω x y + q (x + y) = B x y + q x + q y` (`LinearMap.BilinMap.polarization_cocycle`).

A pairing `B : X × Y → C` gives such a `B` on `W = X × Y`, its **polarized form**
`((x, y), (x', y')) ↦ B x y'` (`LinearMap.polarizedForm`). Its skew part
`((x, y), (x', y')) ↦ B x y' - B x' y` is alternating, and it is the symplectic form of `W` for
which `X` and `Y` are complementary Lagrangians when `B` is a perfect pairing; the polarized
form is the bilinear map of the polarized coordinates of the Heisenberg group of `W`.

## Main definitions

* `LinearMap.polarizedForm`: the bilinear map `((x, y), (x', y')) ↦ B x y'` on `X × Y` of a
  pairing `B : X × Y → C`.

## Main results

* `LinearMap.IsAlt.invOf_two_smul_sub_flip`: `⅟2 • ω - (⅟2 • ω)ᵀ = ω` for alternating `ω` when
  `2` is invertible.
* `LinearMap.BilinMap.polarization_cocycle`: `⅟2 • (B - Bᵀ) x y + q (x + y) = B x y + q x + q y`
  for `q x = ⅟2 • B x x` when `2` is invertible.
* `LinearMap.isAlt_polarizedForm_sub_flip`: the skew part of a polarized form is alternating.

## References

* A. Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964), I.§3.
* S. Kudla, *Notes on the local theta correspondence* (1996), I.2, for polarized coordinates.
-/

public section

namespace LinearMap.IsAlt

variable {R W C : Type*} [CommSemiring R] [AddCommMonoid W] [Module R W]
  [AddCommGroup C] [Module R C]

/-- **The skew part of the half-form `ω / 2` is `ω` itself**: for an alternating bilinear map `ω`
with `2` invertible, `⅟2 • ω - (⅟2 • ω)ᵀ = ω`. -/
@[simp]
theorem invOf_two_smul_sub_flip [Invertible (2 : R)] {ω : LinearMap.BilinMap R W C}
    (hω : ω.IsAlt) :
    ⅟(2 : R) • ω - (⅟(2 : R) • ω).flip = ω := by
  ext w v
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.flip_apply, ← hω.neg w v,
    smul_neg, sub_neg_eq_add, invOf_two_smul_add_invOf_two_smul]

end LinearMap.IsAlt

namespace LinearMap.BilinMap

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- **The polarization cocycle identity.** For a bilinear map `B` with `2` invertible, half of
its skew part and its quadratic diagonal satisfy the coboundary relation
`(ω x y)/2 + q(x+y) = B x y + q x + q y`, where `ω = B - Bᵀ` and `q x = B x x / 2`.

Only the additive monoid structure of the source is needed: expanding `B (x + y) (x + y)` by
biadditivity (`LinearMap.map_add`) lets the skew part cancel the mixed term `B y x`, leaving both
diagonal terms `B x x` and `B y y` and combining the two copies of `B x y`. Subtraction is used
only in the target. -/
theorem polarization_cocycle (B : LinearMap.BilinMap R M N) [Invertible (2 : R)] (x y : M) :
    (⅟(2 : R) • (B - B.flip)) x y + ⅟(2 : R) • B (x + y) (x + y)
      = B x y + ⅟(2 : R) • B x x + ⅟(2 : R) • B y y := by
  have hstep : (⅟(2 : R) • (B - B.flip)) x y = ⅟(2 : R) • (B x y - B y x) := by
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.flip_apply]
  have hdiag : B (x + y) (x + y) = B x x + B x y + B y x + B y y := by
    simp only [map_add, LinearMap.add_apply]
    abel
  have hinner : B x y - B y x + (B x x + B x y + B y x + B y y)
      = (2 : R) • B x y + B x x + B y y := by
    rw [two_smul]
    abel
  rw [hstep, hdiag, ← smul_add, hinner]
  simp only [smul_add, invOf_smul_smul]

end LinearMap.BilinMap

namespace LinearMap

variable {R X Y C : Type*} [CommSemiring R] [AddCommMonoid X] [Module R X]
  [AddCommMonoid Y] [Module R Y]

section AddCommMonoid

variable [AddCommMonoid C] [Module R C]

/-- The **polarized form** of a pairing `B : X × Y → C`: the bilinear map
`((x, y), (x', y')) ↦ B x y'` on `X × Y`. Its skew part `((x, y), (x', y')) ↦ B x y' - B x' y`
is the symplectic form of the polarization `X × Y`. -/
def polarizedForm (B : X →ₗ[R] Y →ₗ[R] C) : LinearMap.BilinMap R (X × Y) C :=
  B.compl₁₂ (LinearMap.fst R X Y) (LinearMap.snd R X Y)

@[simp]
theorem polarizedForm_apply (B : X →ₗ[R] Y →ₗ[R] C) (w v : X × Y) :
    B.polarizedForm w v = B w.1 v.2 :=
  (rfl)

end AddCommMonoid

/-- The skew part `((x, y), (x', y')) ↦ B x y' - B x' y` of a polarized form is alternating. -/
theorem isAlt_polarizedForm_sub_flip [AddCommGroup C] [Module R C] (B : X →ₗ[R] Y →ₗ[R] C) :
    (B.polarizedForm - B.polarizedForm.flip).IsAlt := fun w ↦ by
  simp

end LinearMap
