/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Group
public import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Basic
public import TauCeti.Analysis.Complex.UnitDisc.Basic

/-!
# Linearizing coordinates at a point of finite stabilizer

Let `Γ ≤ PSL(2, ℝ)` and let `z` be a point of the upper half-plane whose stabilizer has finite
order `m`. A **linearizing coordinate** at `z` is a biholomorphism of the upper half-plane onto
the open unit disc which carries `z` to the centre of the disc and the stabilizer of `z` to the
rotation action of the `m`-th roots of unity, `m = Nat.card (stabilizer Γ z)`. In such a
coordinate the local quotient by the stabilizer of `z` is the power map `u ↦ u ^ m`.

The disc coordinate `UpperHalfPlane.discCoordinate` centred at `z` is such a coordinate, and so is
each of its rotations by a unit complex number. The biholomorphic disc coordinates fixing the
origin are exactly the rotations, so *every* linearizing coordinate is the disc coordinate composed
with a rotation (`Subgroup.LinearizingCoordinate.exists_rotatedDiscCoordinate`). The local
quotient data a linearizing coordinate carries — the `m`-th power of the coordinate — is therefore
determined up to a scalar of modulus one: it is the elliptic chart of
`Subgroup.stabilizerBallQuotientChart` up to such a scalar, it has the same modulus as the `m`-th
power of the disc coordinate, and its level sets are exactly the orbits of the stabilizer of `z`,
so it descends to the coarse orbit quotient. The rotation by which a stabilizer element acts is
likewise independent of the linearizing coordinate
(`Subgroup.LinearizingCoordinate.smul_eq_rotation`).

## Main declarations

* `Subgroup.LinearizingCoordinate`: a biholomorphism of the upper half-plane onto the disc
  linearizing the stabilizer of `z`.
* `Subgroup.linearizingCoordinateDiscCoordinate` and `Subgroup.rotationLinearizingCoordinate`:
  the disc coordinate, and its rotations by unit complex numbers.
* `Subgroup.LinearizingCoordinate.exists_rotatedDiscCoordinate`: every linearizing coordinate is a
  rotation of the disc coordinate.
* `Subgroup.LinearizingCoordinate.quotientCoordinate`: the local quotient coordinate, with
  `…_eq_smul_discCoordinate`, `…_eq_smul_stabilizerBallQuotientChart`, `…_norm`, `…_smul` and
  `…_eq_iff`.
* `Subgroup.LinearizingCoordinate.smul_eq_iff` and
  `Subgroup.LinearizingCoordinate.smul_eq_rotation`: the rotation attached to a stabilizer
  element does not depend on the linearizing coordinate.

## References

* Hershel Farkas and Irwin Kra, *Riemann Surfaces*, second edition, Chapter I §§4--5.
* Svetlana Katok, *Fuchsian Groups*, University of Chicago Press, 1992, §2.4.
-/

public noncomputable section

open Filter Matrix.ProjectiveSpecialLinearGroup Metric MulAction Set Topology UpperHalfPlane

open scoped Complex.UnitDisc ComplexConjugate MatrixGroups

namespace Subgroup

variable {Γ : Subgroup PSL(2, ℝ)} {z : ℍ} [Finite (stabilizer Γ z)]

/-- **The inverse of the disc coordinate centred at `z` sends the centre of the disc to `z`.** -/
private theorem discCoordinateHomeomorph_symm_zero (z : ℍ) :
    (discCoordinateHomeomorph z).symm 0 = z := by
  refine UpperHalfPlane.ext ?_
  rw [coe_discCoordinateHomeomorph_symm_apply]
  norm_num

/-- The rotation of the open unit disc by a unit complex number, as a homeomorphism of the
disc. -/
private noncomputable def circleRotation (u : Circle) : 𝔻 ≃ₜ 𝔻 where
  toFun w := u • w
  invFun w := u⁻¹ • w
  left_inv w := by
    ext
    simp
  right_inv w := by
    ext
    simp
  continuous_toFun := TauCeti.continuous_circle_smul_unitDisc u
  continuous_invFun := TauCeti.continuous_circle_smul_unitDisc u⁻¹

/-- The disc coordinate centred at `z`, rotated by the unit complex number `u`. -/
private noncomputable def rotatedDiscCoordinate (u : Circle) (z : ℍ) : ℍ ≃ₜ 𝔻 :=
  (discCoordinateHomeomorph z).trans (circleRotation u)

/-- The disc coordinate centred at `z` sends `z` to the centre of the disc. -/
private theorem discCoordinateHomeomorph_map_zero (z : ℍ) :
    discCoordinateHomeomorph z z = 0 := by
  ext
  rw [coe_discCoordinateHomeomorph_apply, discCoordinate_self, Complex.UnitDisc.coe_zero]

/-- The change of disc coordinate of a rotated disc coordinate is the rotation by `u` of the
disc. -/
private theorem rotatedDiscCoordinate_changeOfDiscCoordinate (u : Circle) (z : ℍ) :
    ((Homeomorph.trans (discCoordinateHomeomorph z).symm
      (rotatedDiscCoordinate u z)).toEquiv) = (MulAction.toPerm u : Equiv.Perm 𝔻) := by
  refine Equiv.ext fun w => ?_
  change Homeomorph.trans (discCoordinateHomeomorph z) (circleRotation u)
    ((discCoordinateHomeomorph z).symm w) = (MulAction.toPerm u) w
  rw [Homeomorph.trans_apply, Homeomorph.apply_symm_apply, circleRotation]
  rfl

/-- The change of disc coordinate of the disc coordinate is the identity. -/
private theorem discCoordinate_changeOfDiscCoordinate (z : ℍ) :
    ((Homeomorph.trans (discCoordinateHomeomorph z).symm
      (discCoordinateHomeomorph z)).toEquiv) = (Equiv.refl 𝔻 : Equiv.Perm 𝔻) := by
  refine Equiv.ext fun w => ?_
  change discCoordinateHomeomorph z ((discCoordinateHomeomorph z).symm w) = w
  rw [Homeomorph.apply_symm_apply]

/-- A rotated disc coordinate is the rotation by `u` of the disc coordinate. -/
private theorem rotatedDiscCoordinate_apply (u : Circle) (z τ : ℍ) :
    (rotatedDiscCoordinate u z τ : 𝔻) = u • ((discCoordinateHomeomorph z) τ) := by rfl

/-- A rotated disc coordinate sends the centre of the disc to the centre of the disc. -/
private theorem rotatedDiscCoordinate_map_zero (u : Circle) (z : ℍ) :
    rotatedDiscCoordinate u z z = 0 := by
  refine Complex.UnitDisc.coe_injective ?_
  have happly : (rotatedDiscCoordinate u z z : 𝔻) = u • ((discCoordinateHomeomorph z) z) := by rfl
  rw [happly, Complex.UnitDisc.coe_circle_smul, coe_discCoordinateHomeomorph_apply,
    discCoordinate_self, Complex.UnitDisc.coe_zero, mul_zero]

/-- A **linearizing coordinate** at `z`: a homeomorphism of the upper half-plane onto the open
unit disc which carries `z` to the centre of the disc and the stabilizer of `z` to the rotation
action of the `Nat.card (stabilizer Γ z)`-th roots of unity, and whose change of disc coordinate
from the disc coordinate is a biholomorphic disc coordinate. In such a coordinate the local
quotient by the stabilizer of `z` is the power map `u ↦ u ^ Nat.card (stabilizer Γ z)`.

Biholomorphy of the change of disc coordinate is a field, phrased as a membership in
`TauCeti.unitDiscAut` — the automorphism group of the disc, whose membership criterion
`TauCeti.mem_unitDiscAut` is the one available outside the file of the definition. Two
coordinates of this kind are available: the disc coordinate itself, whose change of disc
coordinate is the identity, and its rotations, whose change of disc coordinate is the
corresponding rotation of the disc. -/
structure LinearizingCoordinate (Γ : Subgroup PSL(2, ℝ)) (z : ℍ)
    [Finite (stabilizer Γ z)] where
  /-- the coordinate, a homeomorphism of the upper half-plane onto the open unit disc -/
  toEquiv : ℍ ≃ₜ 𝔻
  /-- the coordinate sends the fixed point to the centre of the disc -/
  map_zero : toEquiv z = 0
  /-- the stabilizer of `z` acts in the coordinate by its derivative at `z` -/
  smul : ∀ q : stabilizer Γ z, ∀ τ : ℍ,
    (toEquiv (q • τ) : ℂ) = stabilizerDeriv Γ z q * (toEquiv τ : ℂ)
  /-- the change of disc coordinate, from the disc coordinate to the coordinate, is a
  biholomorphic disc coordinate -/
  holomorphy : (Homeomorph.trans (discCoordinateHomeomorph z).symm toEquiv).toEquiv ∈
    TauCeti.unitDiscAut

/-- The **disc coordinate** centred at `z` is a linearizing coordinate of the stabilizer of `z`:
it is the Cayley map `τ ↦ (τ - z) / (τ - conj z)`, it sends `z` to `0`, each element of the
stabilizer of `z` acts in it by its derivative at `z`
(`UpperHalfPlane.discCoordinate_stabilizer_smul`), and its change of disc coordinate is the
identity. -/
def linearizingCoordinateDiscCoordinate : Γ.LinearizingCoordinate z where
  toEquiv := discCoordinateHomeomorph z
  map_zero := discCoordinateHomeomorph_map_zero z
  smul := by
    simpa only [coe_discCoordinateHomeomorph_apply] using discCoordinate_stabilizer_smul Γ z
  holomorphy := by
    rw [discCoordinate_changeOfDiscCoordinate]
    exact Subgroup.one_mem _

/-- **Rotating the disc coordinate.** For a unit complex number `u` the coordinate
`τ ↦ u • (discCoordinate z τ)` is again a linearizing coordinate of the stabilizer of `z`: it
acts the same way on the stabilizer, and its change of disc coordinate is the rotation of the
disc by `u`, a biholomorphic disc coordinate
(`TauCeti.unitDiscStandardAutomorphismEquiv_zero_mem_unitDiscRotation`). -/
def rotationLinearizingCoordinate (u : Circle) : Γ.LinearizingCoordinate z where
  toEquiv := rotatedDiscCoordinate u z
  map_zero := rotatedDiscCoordinate_map_zero u z
  smul := by
    intro q τ
    rw [rotatedDiscCoordinate_apply u z (q • τ), rotatedDiscCoordinate_apply u z τ,
      Complex.UnitDisc.coe_circle_smul, Complex.UnitDisc.coe_circle_smul,
      coe_discCoordinateHomeomorph_apply, coe_discCoordinateHomeomorph_apply,
      discCoordinate_stabilizer_smul]
    ring
  holomorphy := by
    rw [rotatedDiscCoordinate_changeOfDiscCoordinate,
      ← TauCeti.unitDiscStandardAutomorphismEquiv_zero u]
    exact TauCeti.unitDiscStandardAutomorphismEquiv_mem_unitDiscAut u 0

@[simp]
theorem rotationLinearizingCoordinate_apply (u : Circle) (τ : ℍ) :
    ((rotationLinearizingCoordinate (Γ := Γ) (z := z) u).toEquiv τ : ℂ) =
      (u : ℂ) * discCoordinate z τ := by
  simp only [rotationLinearizingCoordinate, rotatedDiscCoordinate_apply,
    Complex.UnitDisc.coe_circle_smul, coe_discCoordinateHomeomorph_apply]

/-- **A linearizing coordinate is a rotation of the disc coordinate.** The change of disc
coordinate from the disc coordinate to a linearizing coordinate is a biholomorphic disc
coordinate fixing the origin, and the biholomorphic disc coordinates fixing the origin are
exactly the rotations (`TauCeti.mem_unitDiscRotation_iff`): so a linearizing coordinate is the
disc coordinate followed by a rotation, and the local quotient data it carries is determined up
to a scalar of modulus one. -/
theorem LinearizingCoordinate.exists_rotatedDiscCoordinate (φ : Γ.LinearizingCoordinate z) :
    ∃ u : Circle, ∀ τ : ℍ, (φ.toEquiv τ : ℂ) = (u : ℂ) * discCoordinate z τ := by
  -- The change of disc coordinate is a biholomorphic disc coordinate which sends the centre of
  -- the disc, the image of `z` in the disc coordinate, to the centre of the disc, the image of `z`
  -- in `φ`.
  have hzero : ((Homeomorph.trans (discCoordinateHomeomorph z).symm φ.toEquiv).toEquiv) 0 = 0 := by
    have happly : (((Homeomorph.trans (discCoordinateHomeomorph z).symm φ.toEquiv).toEquiv 0
        : 𝔻)) = φ.toEquiv ((discCoordinateHomeomorph z).symm 0) := by rfl
    rw [happly, discCoordinateHomeomorph_symm_zero z, φ.map_zero]
  have hrot : ((Homeomorph.trans (discCoordinateHomeomorph z).symm φ.toEquiv).toEquiv) ∈
      TauCeti.unitDiscRotation :=
    TauCeti.mem_unitDiscRotation_iff.2 ⟨φ.holomorphy, hzero⟩
  rw [TauCeti.unitDiscRotation_eq_range] at hrot
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 hrot
  refine ⟨u, fun τ => ?_⟩
  -- The change of disc coordinate is the rotation by `u`, read off at the disc coordinate of `τ`.
  have hrotate : (((Homeomorph.trans (discCoordinateHomeomorph z).symm φ.toEquiv).toEquiv
      (discCoordinateHomeomorph z τ) : 𝔻)) = u • ((discCoordinateHomeomorph z) τ) := by
    rw [← hu]
    rfl
  have hcomp : (((Homeomorph.trans (discCoordinateHomeomorph z).symm φ.toEquiv).toEquiv
      (discCoordinateHomeomorph z τ) : 𝔻)) = φ.toEquiv τ := by
    have hround : (((Homeomorph.trans (discCoordinateHomeomorph z).symm φ.toEquiv).toEquiv
        (discCoordinateHomeomorph z τ) : 𝔻)) =
        φ.toEquiv ((discCoordinateHomeomorph z).symm (discCoordinateHomeomorph z τ)) := by rfl
    rw [hround, (discCoordinateHomeomorph z).symm_apply_apply]
  rw [← hcomp, hrotate, Complex.UnitDisc.coe_circle_smul, coe_discCoordinateHomeomorph_apply]

/-- The **local quotient coordinate** at `z` read in the linearizing coordinate `φ`: the
`Nat.card (stabilizer Γ z)`-th power of the coordinate, the model of the quotient by the
stabilizer of `z`. Its level sets are exactly the orbits of that stabilizer
(`Subgroup.LinearizingCoordinate.quotientCoordinate_eq_iff`). -/
def LinearizingCoordinate.quotientCoordinate (φ : Γ.LinearizingCoordinate z) (τ : ℍ) : ℂ :=
  (φ.toEquiv τ : ℂ) ^ Nat.card (stabilizer Γ z)

/-- **The change-of-coordinate law for the local quotient coordinate.** The local quotient
coordinate of a linearizing coordinate is the `m`-th power of the disc coordinate multiplied by a
scalar of modulus one, `m = Nat.card (stabilizer Γ z)`: it is determined up to a scalar of
modulus one. -/
theorem LinearizingCoordinate.quotientCoordinate_eq_smul_discCoordinate
    (φ : Γ.LinearizingCoordinate z) (τ : ℍ) :
    ∃ u : Circle, quotientCoordinate φ τ =
      (u : ℂ) ^ Nat.card (stabilizer Γ z) * discCoordinate z τ ^ Nat.card (stabilizer Γ z) := by
  obtain ⟨u, hu⟩ := exists_rotatedDiscCoordinate φ
  refine ⟨u, ?_⟩
  rw [quotientCoordinate, hu τ]
  ring

/-- The local quotient coordinate of a linearizing coordinate is the elliptic chart of
`Subgroup.stabilizerBallQuotientChart` multiplied by a scalar of modulus one, so the local complex
structure of the coarse quotient does not depend on the linearizing coordinate. -/
theorem LinearizingCoordinate.quotientCoordinate_eq_smul_stabilizerBallQuotientChart
    (φ : Γ.LinearizingCoordinate z) {ε : ℝ} (hε : 0 < ε)
    (hopen : IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z ε)) {τ : ℍ}
    (hτ : dist τ z < ε) :
    ∃ u : Circle, quotientCoordinate φ τ =
      (u : ℂ) ^ Nat.card (stabilizer Γ z) *
        stabilizerBallQuotientChart hε hopen (Quotient.mk _ τ) := by
  obtain ⟨u, huτ⟩ := quotientCoordinate_eq_smul_discCoordinate φ τ
  exact ⟨u, by rw [huτ, stabilizerBallQuotientChart_mk hε hopen hτ]⟩

/-- The modulus of the local quotient coordinate is intrinsic: it is the modulus of the `m`-th
power of the disc coordinate, `m = Nat.card (stabilizer Γ z)`, whatever the linearizing
coordinate. -/
theorem LinearizingCoordinate.norm_quotientCoordinate (φ : Γ.LinearizingCoordinate z) (τ : ℍ) :
    ‖quotientCoordinate φ τ‖ = ‖discCoordinate z τ ^ Nat.card (stabilizer Γ z)‖ := by
  obtain ⟨u, hu⟩ := quotientCoordinate_eq_smul_discCoordinate φ τ
  rw [hu, norm_mul, norm_pow, Circle.norm_coe, one_pow, one_mul]

/-- The local quotient coordinate is constant on the orbits of the stabilizer of `z`, since every
element of that stabilizer acts by an `Nat.card (stabilizer Γ z)`-th root of unity. -/
theorem LinearizingCoordinate.quotientCoordinate_smul (φ : Γ.LinearizingCoordinate z)
    (q : stabilizer Γ z) (τ : ℍ) : quotientCoordinate φ (q • τ) = quotientCoordinate φ τ := by
  have hpow : stabilizerDeriv Γ z q ^ Nat.card (stabilizer Γ z) = 1 := by
    have h1 := congrArg (stabilizerDeriv Γ z)
      (pow_card_eq_one' : (q : stabilizer Γ z) ^ Nat.card (stabilizer Γ z) = 1)
    rwa [map_pow, map_one] at h1
  rw [quotientCoordinate, quotientCoordinate, φ.smul q τ, mul_pow, hpow, one_mul]

/-- **The local quotient coordinate of a linearizing coordinate is a complete invariant of the
orbits of the stabilizer of `z`.** Two points have the same local quotient coordinate exactly when
a single element of the stabilizer of `z` carries one to the other, so it descends to the coarse
orbit quotient; by `Subgroup.mem_orbit_stabilizer_iff_discCoordinate_pow_eq_pow` this is the
usual criterion of the cyclic quotient model `u ↦ u ^ m`. -/
theorem LinearizingCoordinate.quotientCoordinate_eq_iff (φ : Γ.LinearizingCoordinate z)
    (τ σ : ℍ) :
    quotientCoordinate φ τ = quotientCoordinate φ σ ↔ τ ∈ orbit (stabilizer Γ z) σ := by
  obtain ⟨u, hu⟩ := exists_rotatedDiscCoordinate φ
  rw [quotientCoordinate, quotientCoordinate, hu τ, hu σ, mul_pow, mul_pow]
  have hu0 : (u : ℂ) ^ Nat.card (stabilizer Γ z) ≠ 0 :=
    pow_ne_zero _ (Circle.coe_ne_zero u)
  constructor
  · intro h
    exact (mem_orbit_stabilizer_iff_discCoordinate_pow_eq_pow Γ z).mpr (mul_left_cancel₀ hu0 h)
  · intro h
    exact congrArg (fun w : ℂ => (u : ℂ) ^ Nat.card (stabilizer Γ z) * w)
      ((mem_orbit_stabilizer_iff_discCoordinate_pow_eq_pow Γ z).mp h)

/-- **The rotation attached to a stabilizer element does not depend on the linearizing
coordinate.** If the `Nat.card (stabilizer Γ z)`-th root of unity by which the element `q` of the
stabilizer of `z` acts in the coordinate `φ` is `ζ`, then `ζ` is the derivative of `q` at `z` —
the image of `q` under the rotation character `Subgroup.stabilizerRotation`. This is read off at
a point whose `φ`-coordinate is nonzero, where the equation can be cancelled. -/
theorem LinearizingCoordinate.smul_eq_iff (φ : Γ.LinearizingCoordinate z) (q : stabilizer Γ z)
    (ζ : rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ) :
    (∀ τ : ℍ, (φ.toEquiv (q • τ) : ℂ) = ((ζ : ℂˣ) : ℂ) * (φ.toEquiv τ : ℂ)) ↔
      ((ζ : ℂˣ) : ℂ) = stabilizerDeriv Γ z q := by
  constructor
  · intro h
    -- Read the relation off at a point of nonzero coordinate: the point of disc coordinate `1 / 2`.
    set w : 𝔻 := ⟨(1 / 2 : ℂ), by norm_num⟩ with hw
    set τ := (discCoordinateHomeomorph z).symm w with hτ
    have hτdisc : discCoordinate z τ = 1 / 2 := by
      rw [hτ, ← coe_discCoordinateHomeomorph_apply, Homeomorph.apply_symm_apply]
      exact congrArg (fun v : 𝔻 => (v : ℂ)) hw
    have hτne : τ ≠ z := by
      intro hEq
      rw [hEq, discCoordinate_self] at hτdisc
      norm_num at hτdisc
    have hφτ : (φ.toEquiv τ : ℂ) ≠ 0 := by
      intro h0
      exact hτne (φ.toEquiv.injective (Complex.UnitDisc.coe_injective
        (by rw [h0, φ.map_zero, Complex.UnitDisc.coe_zero])))
    exact mul_right_cancel₀ hφτ ((h τ).symm.trans (φ.smul q τ))
  · intro h τ
    rw [h]
    exact φ.smul q τ

/-- **A linearizing coordinate linearizes the stabilizer action by the canonical rotations.**
Together with `Subgroup.discCoordinate_smul_eq_rotation_smul` this says that the rotation by
which `q` acts on the disc is the rotation attached to `q` by `Subgroup.stabilizerRotation`,
whichever linearizing coordinate one uses. -/
theorem LinearizingCoordinate.smul_eq_rotation (φ : Γ.LinearizingCoordinate z)
    (q : stabilizer Γ z) :
    ∀ τ : ℍ, (φ.toEquiv (q • τ) : ℂ) =
      ((stabilizerRotation Γ z q : ℂˣ) : ℂ) * (φ.toEquiv τ : ℂ) := by
  refine (smul_eq_iff φ q (stabilizerRotation Γ z q)).2 ?_
  rw [coe_stabilizerRotation]

end Subgroup
