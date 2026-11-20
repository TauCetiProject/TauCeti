/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.WeightedCircle.Basic

/-!
# Weighted circle quotients with a common factor of the weights

Let the circle act on `ℂ²` with positive weights `a` and `b`,
`u • (z₁, z₂) = (u ^ a z₁, u ^ b z₂)` (`TauCeti.Toric.weightedRotation`), and let
`E = {a |z₁|² + b |z₂|² = 2 ε}` be a level of its moment map (`TauCeti.Toric.weightedEllipsoid`).
When the weights have a common factor `d`, say `a = d a'` and `b = d b'`, the action is not
effective, and this file compares it with the action of the weights `(a', b')`.

* **Rescaling.** The rotation by `u` with weights `(a, b)` is the rotation by `u ^ d` with weights
  `(a', b')` (`TauCeti.Toric.weightedRotation_eq_weightedRotation_pow`), so the action factors
  through the `d`-fold covering `u ↦ u ^ d` of the circle. The ellipsoid itself only changes its
  level: `E(a, b, ε) = E(a', b', ε / d)`
  (`TauCeti.Toric.weightedEllipsoid_eq_weightedEllipsoid_div`).
* **Orbits.** Since `u ↦ u ^ d` is surjective, both actions have the same orbits
  (`TauCeti.Toric.exists_weightedRotation_eq_iff_of_eq_mul`), and their orbit spaces are
  homeomorphic (`TauCeti.Toric.commonFactorOrbitHomeomorph`).
* **The quotient for arbitrary positive weights.** Taking `d = gcd(a, b)`, the reduced weights
  `a / d` and `b / d` are coprime, so the weighted Hopf map of the reduced weights,
  `z ↦ [z₁ ^ (b / d) : z₂ ^ (a / d)]`, induces a homeomorphism `E / S¹ ≃ₜ ℂℙ¹`
  (`TauCeti.Toric.reducedWeightedOrbitHomeomorph`). For non-coprime weights the map
  `z ↦ [z₁ ^ b : z₂ ^ a]` does not separate orbits, which is why the reduced exponents appear.

The homeomorphism records only the topology of the quotient. The isotropy is not erased: the
generic stabilizer, which is also the kernel of the action, has order `gcd(a, b)`
(`TauCeti.Toric.natCard_stabilizer_weightedEllipsoid_of_ne_zero`,
`TauCeti.Toric.fixingSubgroup_univ_weightedEllipsoid`), and the stabilizers over the two poles
keep the orders `a` and `b` of the original weights, not the reduced orders `a / d` and `b / d`.

## Main results

* `TauCeti.Toric.weightedRotation_eq_weightedRotation_pow`: the action with weights `(d a', d b')`
  is the action with weights `(a', b')` composed with `u ↦ u ^ d`.
* `TauCeti.Toric.weightedEllipsoid_eq_weightedEllipsoid_div`: `E(d a', d b', ε) = E(a', b', ε / d)`.
* `TauCeti.Toric.exists_weightedRotation_eq_iff_of_eq_mul`: the two actions have the same orbits.
* `TauCeti.Toric.commonFactorOrbitHomeomorph`: the homeomorphism of their orbit spaces.
* `TauCeti.Toric.reducedWeightedOrbitHomeomorph`: `E / S¹ ≃ₜ ℂℙ¹` for all positive weights.

## References

* Eugene Lerman and Susan Tolman, *Hamiltonian torus actions on symplectic orbifolds and toric
  varieties*, Trans. Amer. Math. Soc. 349 (1997), 4201–4230 (weighted projective spaces as
  symplectic quotients, and the ineffective kernel of a torus action).
-/

public section

noncomputable section

open Projectivization
open scoped LinearAlgebra.Projectivization

namespace TauCeti.Toric

variable {a b a' b' d : ℕ} {ε : ℝ}

/-! ### Rescaling the weights -/

/-- **Weights with a common factor.** If `a = d a'` and `b = d b'`, the rotation by `u` with
weights `(a, b)` is the rotation by `u ^ d` with weights `(a', b')`. -/
theorem weightedRotation_eq_weightedRotation_pow (ha : a = d * a') (hb : b = d * b') (u : Circle)
    (z : ℂ × ℂ) : weightedRotation a b u z = weightedRotation a' b' (u ^ d) z := by
  subst ha hb
  ext <;> simp [pow_mul]

/-- **The ellipsoid only changes its level.** If `a = d a'` and `b = d b'` with `d ≠ 0`, the
ellipsoid `a |z₁|² + b |z₂|² = 2 ε` is the ellipsoid `a' |z₁|² + b' |z₂|² = 2 ε / d`. -/
theorem weightedEllipsoid_eq_weightedEllipsoid_div (hd : d ≠ 0) (ha : a = d * a')
    (hb : b = d * b') : weightedEllipsoid a b ε = weightedEllipsoid a' b' (ε / d) := by
  subst ha hb
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd
  ext z
  simp only [mem_weightedEllipsoid, Nat.cast_mul]
  rw [mul_div_assoc', eq_div_iff hd']
  constructor <;> intro h <;> linarith

/-- **Weights with a common factor have the same orbits.** If `a = d a'` and `b = d b'` with
`d ≠ 0`, a point `z` lies in the orbit of `w` for the weights `(a, b)` exactly when it does for
the weights `(a', b')`, since every circle element is a `d`-th power. -/
theorem exists_weightedRotation_eq_iff_of_eq_mul (hd : d ≠ 0) (ha : a = d * a') (hb : b = d * b')
    {z w : ℂ × ℂ} :
    (∃ u : Circle, weightedRotation a b u w = z) ↔
      ∃ u : Circle, weightedRotation a' b' u w = z := by
  have : NeZero d := ⟨hd⟩
  simp_rw [weightedRotation_eq_weightedRotation_pow ha hb]
  refine ⟨fun ⟨u, hu⟩ ↦ ⟨u ^ d, hu⟩, fun ⟨v, hv⟩ ↦ ?_⟩
  obtain ⟨u, rfl⟩ := (Circle.isQuotientCoveringMap_npow d).surjective v
  exact ⟨u, hv⟩

/-! ### Orbit spaces -/

/-- **The orbit spaces of weights with a common factor.** If `a = d a'` and `b = d b'` with
`d ≠ 0`, the ellipsoids `E(a, b, ε)` and `E(a', b', ε / d)` are the same subset of `ℂ²`, and their
orbit spaces under the weighted circle actions are homeomorphic through the identity of that
subset. -/
def commonFactorOrbitHomeomorph (hd : d ≠ 0) (ha : a = d * a') (hb : b = d * b') :
    MulAction.orbitRel.Quotient Circle (weightedEllipsoid a b ε) ≃ₜ
      MulAction.orbitRel.Quotient Circle (weightedEllipsoid a' b' (ε / d)) :=
  Homeomorph.Quotient.congr
    (Homeomorph.setCongr (weightedEllipsoid_eq_weightedEllipsoid_div hd ha hb)) fun z w ↦ by
      simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, ← Subtype.coe_inj,
        coe_smul_weightedEllipsoid]
      exact exists_weightedRotation_eq_iff_of_eq_mul hd ha hb

/-- The homeomorphism of orbit spaces sends the orbit of `z` to the orbit of the same point of
`ℂ²`. -/
@[simp]
theorem commonFactorOrbitHomeomorph_mk (hd : d ≠ 0) (ha : a = d * a') (hb : b = d * b')
    (z : weightedEllipsoid a b ε) :
    commonFactorOrbitHomeomorph hd ha hb (Quotient.mk _ z) =
      Quotient.mk _ ⟨z, (weightedEllipsoid_eq_weightedEllipsoid_div hd ha hb).subset z.2⟩ :=
  (rfl)

/-- **The weighted quotient of the ellipsoid is a sphere, for all positive weights.** For
positive weights `a` and `b` and `ε > 0`, write `d = gcd(a, b)`. The weighted Hopf map of the
coprime reduced weights `(a / d, b / d)`, `z ↦ [z₁ ^ (b / d) : z₂ ^ (a / d)]`, induces a
homeomorphism from the orbit space of the weighted circle action on the ellipsoid
`a |z₁|² + b |z₂|² = 2 ε` onto the complex projective line
(`TauCeti.Toric.reducedWeightedOrbitHomeomorph_mk`). -/
def reducedWeightedOrbitHomeomorph (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    MulAction.orbitRel.Quotient Circle (weightedEllipsoid a b ε) ≃ₜ ℙ ℂ (Fin 2 → ℂ) :=
  have hd := Nat.gcd_pos_of_pos_left b ha
  (commonFactorOrbitHomeomorph hd.ne' (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
      (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm).trans
    (weightedOrbitHomeomorph (Nat.div_pos (Nat.gcd_le_left b ha) hd)
      (Nat.div_pos (Nat.gcd_le_right a hb) hd) (Nat.coprime_div_gcd_div_gcd hd)
      (div_pos hε (Nat.cast_pos.2 hd)))

/-- The homeomorphism `E / S¹ ≃ₜ ℂℙ¹` sends the orbit of `z` to the line through
`(z₁ ^ (b / d), z₂ ^ (a / d))`, with `d = gcd(a, b)`. -/
@[simp]
theorem reducedWeightedOrbitHomeomorph_mk (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε)
    (z : weightedEllipsoid a b ε) :
    reducedWeightedOrbitHomeomorph ha hb hε (Quotient.mk _ z) =
      mk ℂ (weightedHopfVector (a / a.gcd b) (b / a.gcd b) z)
        (weightedHopfVector_ne_zero
          (div_pos hε (Nat.cast_pos.2 (Nat.gcd_pos_of_pos_left b ha)))
          ((weightedEllipsoid_eq_weightedEllipsoid_div (Nat.gcd_pos_of_pos_left b ha).ne'
            (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
            (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm).subset z.2)) := by
  rw [reducedWeightedOrbitHomeomorph, Homeomorph.trans_apply, commonFactorOrbitHomeomorph_mk,
    weightedOrbitHomeomorph_mk, weightedHopf_def]

/-- For coprime weights the homeomorphism `E / S¹ ≃ₜ ℂℙ¹` is
`TauCeti.Toric.weightedOrbitHomeomorph`, induced by the weighted Hopf map `z ↦ [z₁ ^ b : z₂ ^ a]`.
-/
theorem reducedWeightedOrbitHomeomorph_eq_weightedOrbitHomeomorph (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (hε : 0 < ε) :
    reducedWeightedOrbitHomeomorph ha hb hε = weightedOrbitHomeomorph ha hb hab hε := by
  ext q
  induction q using Quotient.inductionOn with | h z => ?_
  rw [reducedWeightedOrbitHomeomorph_mk, weightedOrbitHomeomorph_mk, weightedHopf_def]
  simp only [Nat.Coprime.gcd_eq_one hab, Nat.div_one]

end TauCeti.Toric
