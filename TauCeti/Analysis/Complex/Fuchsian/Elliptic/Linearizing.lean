/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Basic

/-!
# Local linearizing coordinates at a point of finite stabilizer

Let `Γ ≤ PSL(2, ℝ)` and let `z` be a point of the upper half-plane whose stabilizer has finite
order `m`. A **local linearizing coordinate** at `z` is a biholomorphic coordinate on the
invariant hyperbolic disc of radius `ε` about `z` which sends `z` to the centre and in which the
stabilizer of `z` acts by rotations: it is a biholomorphic reparametrization `ψ` of the
Euclidean disc of radius `tanh (ε / 2)`, the image of the invariant disc in the disc coordinate
centred at `z`, fixing `0` and intertwining the rotation action of the `m`-th roots of unity on
the disc with the rotation action on its image (`Subgroup.LinearizingCoordinate`). The stabilizer
of `z` acts on the invariant hyperbolic disc itself, and the disc coordinate centred at `z` turns
that action into the rotation action of the `m`-th roots of unity, so the rotation by which a
stabilizer element acts in a local linearizing coordinate is `Subgroup.stabilizerRotation` in
every one of them (`Subgroup.LinearizingCoordinate.coordinate_smul`).

A local linearizing coordinate is genuinely *local*: its image is its own open set
`Subgroup.LinearizingCoordinate.image`, which is not required to be the whole unit disc, and
the equivariant biholomorphic reparametrizations of a disc are not all rotations. In particular
`w ↦ w (1 + a w ^ m)` is such a reparametrization for small `a`, and the transition between two
local linearizing coordinates is in general a non-trivial automorphism of the quotient.

What does not depend on the choice of the local linearizing coordinate is the local complex
structure defined by the **local quotient coordinate**
`Subgroup.LinearizingCoordinate.quotientCoordinate`, the `m`-th power of the coordinate: the
quotient coordinates of two local linearizing coordinates are related by a biholomorphic
transition, not by equality. The local quotient coordinate is constant on the orbits of the
stabilizer
(`Subgroup.LinearizingCoordinate.quotientCoordinate_smul`), its level sets are exactly those
orbits (`Subgroup.LinearizingCoordinate.quotientCoordinate_eq_iff`), so it is a coordinate on
the quotient of the invariant disc by the stabilizer of `z`; and the quotient coordinates of two
local linearizing coordinates are related by a map that is holomorphic with holomorphic inverse
between the open sets of quotient-coordinate values — a biholomorphic transition
(`Subgroup.LinearizingCoordinate.exists_quotientCoordinate_trans`) — obtained by descending the
change of coordinate through `u ↦ u ^ m` with `TauCeti.differentiableOn_descendPow`. Since the
rotation by which an element of the stabilizer acts is `Subgroup.stabilizerRotation`, the same
rotation appears in every local linearizing coordinate
(`Subgroup.LinearizingCoordinate.coordinate_smul`).

The two coordinates available by construction are the disc coordinate centred at `z` and its
rotation by a root of unity (`Subgroup.LinearizingCoordinate.discCoordinate`,
`Subgroup.LinearizingCoordinate.rotation`); for the disc coordinate the quotient coordinate is
`discCoordinate z τ ^ m`, the coordinate of `Subgroup.stabilizerBallQuotientHomeomorph` and
`Subgroup.stabilizerBallQuotientChart`, and a rotation leaves it unchanged
(`Subgroup.LinearizingCoordinate.quotientCoordinate_rotation`). Independence from the choice of
the invariant disc is `Subgroup.stabilizerBallQuotientChart_trans_apply`.

## Main declarations

* `Subgroup.LinearizingCoordinate`: a local biholomorphic coordinate linearizing the stabilizer
  of `z` on the invariant disc of radius `ε`.
* `Subgroup.LinearizingCoordinate.coordinate`, `…_smul`, `…_injective`: the coordinate of a point
  of the invariant disc and the action of the stabilizer on it.
* `Subgroup.LinearizingCoordinate.image`, `…_isOpen_image`, `…_mem_image_iff`: the open image of
  the reparametrization, the set of coordinate values.
* `Subgroup.LinearizingCoordinate.transFun`, `…_transFun_coordinate`, `…_transFun_transFun` and
  `Subgroup.LinearizingCoordinate.differentiableOn_transFun`: the biholomorphic change of local
  linearizing coordinate between two local linearizing coordinates.
* `Subgroup.LinearizingCoordinate.quotientCoordinate` with `…_smul` and `…_eq_iff`, and
  `Subgroup.LinearizingCoordinate.quotientImage` with `…_isOpen_quotientImage` and
  `…_mem_quotientImage_iff`:
  the local quotient coordinate, its invariance, its level sets, and the open set of its values.
* `Subgroup.LinearizingCoordinate.quotientCoordinateTrans`,
  `…_quotientCoordinateTrans_mem_quotientImage` and `…_exists_quotientCoordinate_trans`: the
  transition between the quotient coordinates of two local linearizing coordinates, the set of
  quotient-coordinate values it maps into, and the biholomorphic transition it is.
* `Subgroup.LinearizingCoordinate.discCoordinate` and `…_rotation`: the two reparametrizations
  available by construction, with `…_quotientCoordinate` and `…_quotientCoordinate_rotation`
  computing their quotient coordinates.

## References

* Hershel Farkas and Irwin Kra, *Riemann Surfaces*, second edition, Chapter IV §9: the
  stabilizer of a point of a group of Möbius transformations is cyclic when it is finite, and at
  an elliptic fixed point it is generated by the rotation `z ↦ e ^ (2 * π * I / v) * z`, the
  quotient carrying the local coordinate `z ^ v`, the `v`-th power, which that rotation leaves
  fixed (§IV.9.11).
* Svetlana Katok, *Fuchsian Groups*, University of Chicago Press, 1992, §2.4.
-/

public noncomputable section

open Filter Metric MulAction Set Topology UpperHalfPlane

open scoped ComplexConjugate MatrixGroups

namespace Subgroup

variable {Γ : Subgroup PSL(2, ℝ)} {z : ℍ} {ε : ℝ} [Finite (stabilizer Γ z)]

/-- **A local linearizing coordinate** at `z` on the invariant hyperbolic disc of radius `ε`: a
biholomorphic reparametrization `toFun` of the Euclidean disc of radius `Real.tanh (ε / 2)`, the
image of the invariant disc in the disc coordinate centred at `z`, which fixes `0` and intertwines
the rotation action of the `Nat.card (stabilizer Γ z)`-th roots of unity on the disc with the
rotation action on its image. The coordinate of a point `τ` of the invariant disc is then
`Subgroup.LinearizingCoordinate.coordinate ψ τ = toFun (discCoordinate z τ)`, a biholomorphic
coordinate of the invariant disc; the stabilizer of `z` acts on that disc, and by
`Subgroup.LinearizingCoordinate.coordinate_smul` it acts in this coordinate by the rotation
`Subgroup.stabilizerRotation`, so the quotient by the stabilizer is the power map `u ↦ u ^ m`,
`m = Nat.card (stabilizer Γ z)`.

The image `image` of the reparametrization is only required to be open, not to be the whole
Euclidean disc: local linearizing coordinates are not all rotations of the disc coordinate, the
equivariant biholomorphic reparametrizations of a disc being an infinite-dimensional family.
Biholomorphy is the requirement that `toFun` and `invFun` be holomorphic on the disc and on
`image` respectively and inverse to one another there, the holomorphy of `invFun` following too
from that of `toFun` by the inverse function theorem, the image being open
(`Subgroup.LinearizingCoordinate.isOpen_image`). -/
structure LinearizingCoordinate (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) (ε : ℝ)
    [Finite (stabilizer Γ z)] where
  /-- the reparametrization of the disc coordinate -/
  toFun : ℂ → ℂ
  /-- the inverse reparametrization, on the image of `toFun` -/
  invFun : ℂ → ℂ
  /-- the image of the reparametrization -/
  image : Set ℂ
  /-- the image is the image of the disc of the invariant disc; it is open, by
  `Subgroup.LinearizingCoordinate.isOpen_image` -/
  image_eq : image = toFun '' Metric.ball 0 (Real.tanh (ε / 2))
  /-- the reparametrization is holomorphic on the disc of the invariant disc -/
  differentiable : DifferentiableOn ℂ toFun (Metric.ball 0 (Real.tanh (ε / 2)))
  /-- the inverse reparametrization is holomorphic on the image -/
  differentiable_inv : DifferentiableOn ℂ invFun image
  /-- the two functions are inverse on the disc of the invariant disc -/
  left_inv : ∀ w : ℂ, w ∈ Metric.ball 0 (Real.tanh (ε / 2)) → invFun (toFun w) = w
  /-- the two functions are inverse on the image -/
  right_inv : ∀ w ∈ image, toFun (invFun w) = w
  /-- the reparametrization fixes the centre -/
  zero : toFun 0 = 0
  /-- the reparametrization is the identity outside the disc of the invariant disc, the choice
  which leaves the disc coordinate the identity reparametrization; it makes a local linearizing
  coordinate determined by its values on that disc (`Subgroup.LinearizingCoordinate.ext`) -/
  toFun_eq_id : ∀ w : ℂ, w ∉ Metric.ball 0 (Real.tanh (ε / 2)) → toFun w = w
  /-- the inverse reparametrization is the identity outside the image, so that it too is
  determined by the values of the reparametrization on the disc of the invariant disc
  (`Subgroup.LinearizingCoordinate.ext`) -/
  invFun_eq_id : ∀ w : ℂ, w ∉ image → invFun w = w
  /-- the reparametrization intertwines the rotation action of the roots of unity on the disc
  with the rotation action on its image -/
  smul : ∀ ζ : rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ, ∀ w : ℂ,
    w ∈ Metric.ball 0 (Real.tanh (ε / 2)) → toFun (ζ • w) = ζ • toFun w

omit [Finite (stabilizer Γ z)] in
/-- The disc coordinate of a point of the invariant disc lies in the disc of the invariant
disc, the domain of a reparametrization. -/
private theorem mem_ball_discCoordinate (τ : stabilizerBall Γ z ε) :
    discCoordinate z (τ : ℍ) ∈ Metric.ball 0 (Real.tanh (ε / 2)) := by
  have hball : (τ : ℍ) ∈ Metric.ball z ε := Metric.mem_ball.mpr ((mem_stabilizerBall Γ z ε).1 τ.2)
  rw [mem_ball_zero_iff]
  exact (mem_ball_iff_norm_discCoordinate_lt (z := z) (τ := (τ : ℍ)) (ε := ε)).mp hball

/-- A rotation of a point of the disc of the invariant disc lies in it, the modulus of a root of
unity being one by `Complex.norm_eq_one_of_mem_rootsOfUnity`. -/
private theorem mem_ball_smul (ζ : rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ) {w : ℂ}
    (hw : w ∈ Metric.ball 0 (Real.tanh (ε / 2))) :
    ζ • w ∈ Metric.ball 0 (Real.tanh (ε / 2)) := by
  rw [mem_ball_zero_iff] at hw ⊢
  rw [rootsOfUnity.smul_eq_mul, norm_mul, Complex.norm_eq_one_of_mem_rootsOfUnity ζ.2, one_mul]
  exact hw

/-- The reparametrization of a local linearizing coordinate is injective on the disc of the
invariant disc. -/
theorem LinearizingCoordinate.injOn_ball (ψ : Γ.LinearizingCoordinate z ε) :
    Set.InjOn ψ.toFun (Metric.ball 0 (Real.tanh (ε / 2))) := by
  rintro u hu v hv huv
  have hu' := ψ.left_inv u hu
  have hv' := ψ.left_inv v hv
  rw [huv] at hu'
  exact hu'.symm.trans hv'

/-- The inverse reparametrization of a local linearizing coordinate takes a point of the image
back into the disc of the invariant disc. -/
theorem LinearizingCoordinate.mem_ball_invFun (ψ : Γ.LinearizingCoordinate z ε)
    {u : ℂ} (hu : u ∈ ψ.image) : ψ.invFun u ∈ Metric.ball 0 (Real.tanh (ε / 2)) := by
  rw [ψ.image_eq, Set.mem_image] at hu
  obtain ⟨w, hw, rfl⟩ := hu
  rw [ψ.left_inv w hw]
  exact hw

/-- **The coordinate of a point of the invariant disc in a local linearizing coordinate**: the
reparametrized disc coordinate, a biholomorphic coordinate on the invariant hyperbolic disc of
radius `ε` about `z` centred at `z` in which the stabilizer of `z` acts by its rotation
`Subgroup.stabilizerRotation`
(`Subgroup.LinearizingCoordinate.coordinate_smul`). -/
def LinearizingCoordinate.coordinate (ψ : Γ.LinearizingCoordinate z ε)
    (τ : stabilizerBall Γ z ε) : ℂ := ψ.toFun (discCoordinate z (τ : ℍ))

/-- A point of the invariant disc has coordinate `0` in a local linearizing coordinate exactly
when it is the centre: the coordinate is centred at the centre. -/
@[simp]
theorem LinearizingCoordinate.coordinate_eq_zero_iff
    (ψ : Γ.LinearizingCoordinate z ε) (τ : stabilizerBall Γ z ε) :
    coordinate ψ τ = 0 ↔ (τ : ℍ) = z := by
  have hε : 0 < ε := lt_of_le_of_lt dist_nonneg ((mem_stabilizerBall Γ z ε).1 τ.2)
  constructor
  · intro h
    have h' : ψ.toFun (discCoordinate z (τ : ℍ)) = ψ.toFun 0 := by
      have h'' : ψ.toFun (discCoordinate z (τ : ℍ)) = 0 := h
      rw [h'', ψ.zero]
    have hinj : discCoordinate z (τ : ℍ) = 0 :=
      ψ.injOn_ball (mem_ball_discCoordinate τ)
        (Metric.mem_ball_self (Real.tanh_pos_of_pos (by linarith : 0 < ε / 2))) h'
    exact discCoordinate_eq_zero_iff.mp hinj
  · intro hτ
    have hmem : (z : ℍ) ∈ (stabilizerBall Γ z ε : Set ℍ) :=
      (mem_stabilizerBall Γ z ε).2 (by rw [dist_self]; exact hε)
    have hτ' : τ = ⟨z, hmem⟩ := Subtype.ext hτ
    rw [hτ']
    simp only [coordinate, discCoordinate_self]
    exact ψ.zero

/-- The coordinate of a local linearizing coordinate is injective on the invariant disc. -/
theorem LinearizingCoordinate.coordinate_injective (ψ : Γ.LinearizingCoordinate z ε) :
    Function.Injective (coordinate ψ) :=
  fun _ _ h => Subtype.ext (discCoordinate_injective z
    (ψ.injOn_ball (mem_ball_discCoordinate _) (mem_ball_discCoordinate _) h))

/-- **The stabilizer of `z` acts in the coordinate of a local linearizing coordinate by its
rotation.** The rotation does not depend on the local linearizing coordinate: it is
`Subgroup.stabilizerRotation Γ z q`, the derivative of `q` at `z`. -/
theorem LinearizingCoordinate.coordinate_smul (ψ : Γ.LinearizingCoordinate z ε)
    (q : stabilizer Γ z) (τ : stabilizerBall Γ z ε) :
    coordinate ψ (q • τ) = ((stabilizerRotation Γ z q : ℂˣ) : ℂ) * coordinate ψ τ := by
  have hcoord : discCoordinate z ((q • τ : stabilizerBall Γ z ε) : ℍ)
      = ((stabilizerRotation Γ z q : ℂˣ) : ℂ) * discCoordinate z (τ : ℍ) := by
    rw [SubMulAction.val_smul, discCoordinate_smul_eq_rotation_smul, rootsOfUnity.smul_eq_mul,
      coe_stabilizerRotation]
  have hsmul : ψ.toFun (((stabilizerRotation Γ z q) • (discCoordinate z (τ : ℍ))) : ℂ)
      = stabilizerRotation Γ z q • ψ.toFun (discCoordinate z (τ : ℍ)) :=
    ψ.smul (stabilizerRotation Γ z q) (discCoordinate z (τ : ℍ)) (mem_ball_discCoordinate τ)
  simp only [coordinate]
  rw [hcoord]
  calc ψ.toFun (((stabilizerRotation Γ z q) • (discCoordinate z (τ : ℍ))) : ℂ)
      = stabilizerRotation Γ z q • ψ.toFun (discCoordinate z (τ : ℍ)) := hsmul
    _ = ((stabilizerRotation Γ z q : ℂˣ) : ℂ) * ψ.toFun (discCoordinate z (τ : ℍ)) :=
      rootsOfUnity.smul_eq_mul (stabilizerRotation Γ z q) (ψ.toFun (discCoordinate z (τ : ℍ)))
    _ = ((stabilizerRotation Γ z q : ℂˣ) : ℂ) * coordinate ψ τ := rfl

/-- **A point is a coordinate value of a local linearizing coordinate** exactly when it lies in
the image of the reparametrization. -/
@[simp]
theorem LinearizingCoordinate.mem_image_iff (ψ : Γ.LinearizingCoordinate z ε) (u : ℂ) :
    u ∈ ψ.image ↔ ∃ τ : stabilizerBall Γ z ε, u = coordinate ψ τ := by
  constructor
  · intro hu
    rw [ψ.image_eq, Set.mem_image] at hu
    obtain ⟨w, hw, hwu⟩ := hu
    have hmem : w ∈ discCoordinate z '' Metric.ball z ε := by
      rw [UpperHalfPlane.image_discCoordinate_ball]
      exact hw
    obtain ⟨τ, hτ, hdt⟩ := (Set.mem_image (discCoordinate z) (Metric.ball z ε) w).mp hmem
    refine ⟨⟨τ, (mem_stabilizerBall Γ z ε).2 hτ⟩, ?_⟩
    simp only [coordinate]
    rw [hdt]
    exact hwu.symm
  · rintro ⟨τ, rfl⟩
    rw [ψ.image_eq, Set.mem_image]
    exact ⟨discCoordinate z (τ : ℍ), mem_ball_discCoordinate τ, rfl⟩

/-- **The image of a local linearizing coordinate is open**, being the image of a disc of
positive radius under a holomorphic reparametrization which is not constant there. -/
theorem LinearizingCoordinate.isOpen_image (hε : 0 < ε) (ψ : Γ.LinearizingCoordinate z ε) :
    IsOpen ψ.image := by
  have hpos : 0 < Real.tanh (ε / 2) := Real.tanh_pos_of_pos (by linarith)
  have hball : (0 : ℂ) ∈ Metric.ball 0 (Real.tanh (ε / 2)) := Metric.mem_ball_self hpos
  have hhalf : (Real.tanh (ε / 2) / 2 : ℂ) ∈ Metric.ball 0 (Real.tanh (ε / 2)) := by
    rw [mem_ball_zero_iff, Complex.norm_div, Complex.norm_ofNat,
      Complex.norm_of_nonneg hpos.le]
    linarith
  have hpre : IsPreconnected (Metric.ball (0 : ℂ) (Real.tanh (ε / 2))) :=
    (convex_ball (0 : ℂ) (Real.tanh (ε / 2))).isPreconnected
  rcases (ψ.differentiable.analyticOnNhd Metric.isOpen_ball).is_constant_or_isOpen hpre with
    ⟨w, hw⟩ | hopen
  · -- the reparametrization is not constant on the disc, by its inverse at two points of it
    have e0 : ψ.invFun w = 0 := by
      have e := ψ.left_inv 0 hball
      rw [hw 0 hball] at e
      exact e
    have e1 : ψ.invFun w = (Real.tanh (ε / 2) / 2 : ℂ) := by
      have e := ψ.left_inv (Real.tanh (ε / 2) / 2) hhalf
      rw [hw _ hhalf] at e
      exact e
    have hzero : (Real.tanh (ε / 2) / 2 : ℂ) = 0 := e1.symm.trans e0
    have hnorm := congrArg (fun w : ℂ => ‖w‖) hzero
    rw [norm_zero, Complex.norm_div, Complex.norm_ofNat, Complex.norm_of_nonneg hpos.le] at hnorm
    linarith
  · rw [ψ.image_eq]
    exact hopen _ subset_rfl Metric.isOpen_ball

/-- **The local quotient coordinate** in a local linearizing coordinate: the
`Nat.card (stabilizer Γ z)`-th power of the coordinate, the model of the quotient of the
invariant disc by the stabilizer of `z`, `m = Nat.card (stabilizer Γ z)`. Its level sets are the
orbits of that stabilizer (`Subgroup.LinearizingCoordinate.quotientCoordinate_eq_iff`), so it is a
coordinate on that quotient, and it is independent of the local linearizing coordinate up to the
biholomorphic transition of
`Subgroup.LinearizingCoordinate.exists_quotientCoordinate_trans`. -/
def LinearizingCoordinate.quotientCoordinate (ψ : Γ.LinearizingCoordinate z ε)
    (τ : stabilizerBall Γ z ε) : ℂ := coordinate ψ τ ^ Nat.card (stabilizer Γ z)

/-- The local quotient coordinate is constant on the orbits of the stabilizer of `z`, since the
stabilizer acts by a `Nat.card (stabilizer Γ z)`-th root of unity. -/
@[simp]
theorem LinearizingCoordinate.quotientCoordinate_smul (ψ : Γ.LinearizingCoordinate z ε)
    (q : stabilizer Γ z) (τ : stabilizerBall Γ z ε) :
    quotientCoordinate ψ (q • τ) = quotientCoordinate ψ τ := by
  rw [quotientCoordinate, quotientCoordinate, coordinate_smul, ← rootsOfUnity.smul_eq_mul,
    rootsOfUnity.smul_pow]

/-- **The orbits of the stabilizer of `z` on the invariant disc are the orbits of the roots of
unity in the coordinate of a local linearizing coordinate**: the reparametrization of the disc
coordinate does not change which points lie in the same orbit, so the orbit relation of the
stabilizer of `z` on the invariant disc does not depend on the local linearizing coordinate. The
roots of unity act on `ℂ` by multiplication, as on the disc
`Subgroup.stabilizerBallHomeomorph_smul`. -/
theorem LinearizingCoordinate.orbitRel_iff (ψ : Γ.LinearizingCoordinate z ε)
    (τ σ : stabilizerBall Γ z ε) :
    orbitRel (stabilizer Γ z) (stabilizerBall Γ z ε) τ σ ↔
      orbitRel (rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ) ℂ
        (coordinate ψ τ) (coordinate ψ σ) := by
  rw [orbitRel_apply, orbitRel_apply, mem_orbit_iff, mem_orbit_iff]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨stabilizerRotation Γ z q, ?_⟩
    calc stabilizerRotation Γ z q • (coordinate ψ σ : ℂ)
        = ((stabilizerRotation Γ z q : ℂˣ) : ℂ) * coordinate ψ σ :=
          (rootsOfUnity.smul_eq_mul _ _).symm
      _ = coordinate ψ (q • σ) := (coordinate_smul ψ q σ).symm
      _ = coordinate ψ τ := congrArg (coordinate ψ) hq
  · rintro ⟨ζ, hζ⟩
    let q := (stabilizerRotationEquiv Γ z).symm ζ
    have hq : stabilizerRotation Γ z q = ζ := by
      rw [← coe_stabilizerRotationEquiv]
      exact (stabilizerRotationEquiv Γ z).apply_symm_apply ζ
    simp only [coordinate] at hζ
    have h1 : coordinate ψ (q • σ) = stabilizerRotation Γ z q • (coordinate ψ σ : ℂ) := by
      rw [coordinate_smul, rootsOfUnity.smul_eq_mul]
    rw [hq] at h1
    refine ⟨q, Subtype.ext ?_⟩
    exact congrArg (fun p : stabilizerBall Γ z ε => (p : ℍ)) (coordinate_injective ψ (h1.trans hζ))

/-- The local quotient coordinate is a complete invariant of the orbits of the stabilizer of `z`
on the invariant disc: two points of the invariant disc have the same local quotient coordinate
exactly when a single element of the stabilizer carries one to the other, that is, when they lie
in the same orbit of the stabilizer of `z`. Hence the local quotient coordinate is a coordinate on
the quotient of the invariant disc by that stabilizer, which the disc coordinate identifies with
the coordinate of the chart `Subgroup.stabilizerBallQuotientChart` on the coarse orbit quotient
`Γ \ ℍ`
(`Subgroup.LinearizingCoordinate.quotientCoordinate_discCoordinate`). -/
theorem LinearizingCoordinate.quotientCoordinate_eq_iff (ψ : Γ.LinearizingCoordinate z ε)
    (τ σ : stabilizerBall Γ z ε) :
    quotientCoordinate ψ τ = quotientCoordinate ψ σ ↔
      orbitRel (stabilizer Γ z) (stabilizerBall Γ z ε) τ σ := by
  rw [quotientCoordinate, quotientCoordinate, ψ.orbitRel_iff,
    TauCeti.orbitRel_rootsOfUnity_apply (NeZero.ne _)]

/-- **The set of quotient-coordinate values of a local linearizing coordinate**: the
`Nat.card (stabilizer Γ z)`-th powers of the coordinate values, which is the image of the `m`-th
power, `m = Nat.card (stabilizer Γ z)`, of the image `Subgroup.LinearizingCoordinate.image` of
the reparametrization, and is an open set by
`Subgroup.LinearizingCoordinate.isOpen_quotientImage`. -/
def LinearizingCoordinate.quotientImage (ψ : Γ.LinearizingCoordinate z ε) : Set ℂ :=
  (· ^ Nat.card (stabilizer Γ z)) '' ψ.image

/-- **A point is a quotient-coordinate value of a local linearizing coordinate** exactly when it
is the `Nat.card (stabilizer Γ z)`-th power of a coordinate value. -/
@[simp]
theorem LinearizingCoordinate.mem_quotientImage_iff (ψ : Γ.LinearizingCoordinate z ε) (w : ℂ) :
    w ∈ ψ.quotientImage ↔ ∃ τ : stabilizerBall Γ z ε, w = quotientCoordinate ψ τ := by
  constructor
  · intro hw
    rw [quotientImage, Set.mem_image] at hw
    obtain ⟨u, hu, hw⟩ := hw
    obtain ⟨τ, rfl⟩ := (ψ.mem_image_iff u).mp hu
    refine ⟨τ, ?_⟩
    simpa only [quotientCoordinate] using hw.symm
  · rintro ⟨τ, rfl⟩
    rw [quotientImage, Set.mem_image]
    exact ⟨coordinate ψ τ, (ψ.mem_image_iff (coordinate ψ τ)).mpr ⟨τ, rfl⟩, rfl⟩

/-- **The set of quotient-coordinate values of a local linearizing coordinate is open**: it is the
image of the open image of the reparametrization under the power map `u ↦ u ^ m`, which is an open
map, being a non-constant holomorphic map (`Complex.isOpenQuotientMap_pow`). -/
theorem LinearizingCoordinate.isOpen_quotientImage (hε : 0 < ε)
    (ψ : Γ.LinearizingCoordinate z ε) : IsOpen ψ.quotientImage := by
  rw [quotientImage]
  exact (Complex.isOpenQuotientMap_pow (Nat.card (stabilizer Γ z))).isOpenMap _
    (ψ.isOpen_image hε)

/-- **The change of local linearizing coordinate** between two local linearizing coordinates on
the invariant disc: the reparametrization `ψ'` pulled back by the inverse reparametrization `ψ`.
On the image `Subgroup.LinearizingCoordinate.image` of `ψ` it is a biholomorphism onto the image
of `ψ'` intertwining the rotation action
(`Subgroup.LinearizingCoordinate.transFun_smul`), taking a coordinate value to the
corresponding coordinate value
(`Subgroup.LinearizingCoordinate.transFun_coordinate`), and its inverse being the change of
coordinate in the other direction
(`Subgroup.LinearizingCoordinate.transFun_transFun`). -/
def LinearizingCoordinate.transFun (ψ ψ' : Γ.LinearizingCoordinate z ε) : ℂ → ℂ :=
  fun u => ψ'.toFun (ψ.invFun u)

/-- **The change of local linearizing coordinate takes a coordinate value to a coordinate
value**: it carries a point of the image `Subgroup.LinearizingCoordinate.image` of `ψ` to a
point of the image of `ψ'`, so the change of coordinate is a map between the two open sets of
coordinate values. -/
theorem LinearizingCoordinate.transFun_mem_image (ψ ψ' : Γ.LinearizingCoordinate z ε)
    {u : ℂ} (hu : u ∈ ψ.image) : transFun ψ ψ' u ∈ ψ'.image := by
  rw [ψ'.image_eq, Set.mem_image]
  exact ⟨ψ.invFun u, ψ.mem_ball_invFun hu, rfl⟩

/-- **The change of local linearizing coordinate takes a coordinate value to a coordinate
value**, which is how a point of the invariant disc is read in the second local linearizing
coordinate once it is read in the first one. -/
@[simp]
theorem LinearizingCoordinate.transFun_coordinate (ψ ψ' : Γ.LinearizingCoordinate z ε)
    (τ : stabilizerBall Γ z ε) :
    transFun ψ ψ' (coordinate ψ τ) = coordinate ψ' τ := by
  simp only [transFun, coordinate]
  rw [ψ.left_inv (discCoordinate z (τ : ℍ)) (mem_ball_discCoordinate τ)]

/-- **The inverse reparametrization of a local linearizing coordinate is equivariant for the
rotations**: it intertwines the rotation action of the roots of unity on the image with the
rotation action of the roots of unity on the disc. -/
theorem LinearizingCoordinate.invFun_smul (ψ : Γ.LinearizingCoordinate z ε) {u : ℂ}
    (hu : u ∈ ψ.image) (ζ : rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ) :
    ψ.invFun (ζ • u) = ζ • ψ.invFun u := by
  have hw := ψ.mem_ball_invFun hu
  have hwu : ψ.toFun (ζ • ψ.invFun u) = ζ • u := by
    rw [ψ.smul ζ _ hw, ψ.right_inv u hu]
  calc ψ.invFun (ζ • u) = ψ.invFun (ψ.toFun (ζ • ψ.invFun u)) := by rw [hwu]
    _ = ζ • ψ.invFun u := ψ.left_inv (ζ • ψ.invFun u) (mem_ball_smul ζ hw)

/-- The change of local linearizing coordinate intertwines the rotation action, being the pullback
of an equivariant reparametrization by an equivariant inverse. -/
theorem LinearizingCoordinate.transFun_smul (ψ ψ' : Γ.LinearizingCoordinate z ε) {u : ℂ}
    (hu : u ∈ ψ.image) (ζ : rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ) :
    transFun ψ ψ' (ζ • u) = ζ • transFun ψ ψ' u := by
  simp only [transFun]
  have hkey : ψ.invFun (ζ • u) = ζ • ψ.invFun u := ψ.invFun_smul hu ζ
  exact (congrArg ψ'.toFun hkey).trans (ψ'.smul ζ _ (ψ.mem_ball_invFun hu))

/-- The changes of local linearizing coordinate in the two directions are inverse: the change of
coordinate is a biholomorphism of the images of the reparametrizations. -/
@[simp]
theorem LinearizingCoordinate.transFun_transFun (ψ ψ' : Γ.LinearizingCoordinate z ε)
    {u : ℂ} (hu : u ∈ ψ.image) : transFun ψ' ψ (transFun ψ ψ' u) = u := by
  simp only [transFun]
  rw [ψ'.left_inv _ (ψ.mem_ball_invFun hu), ψ.right_inv u hu]

/-- The change of local linearizing coordinate is holomorphic on the image of the reparametrization,
being the composition of the inverse reparametrization, holomorphic there, with the
reparametrization, holomorphic on the disc of the invariant disc. -/
theorem LinearizingCoordinate.differentiableOn_transFun (ψ ψ' : Γ.LinearizingCoordinate z ε) :
    DifferentiableOn ℂ (transFun ψ ψ') ψ.image :=
  ψ'.differentiable.comp ψ.differentiable_inv (fun _ hu => ψ.mem_ball_invFun hu)

/-- **The transition of the local quotient coordinates** of two local linearizing coordinates: the
descent through `u ↦ u ^ m`, `m = Nat.card (stabilizer Γ z)`, of the `m`-th power of the change of
local linearizing coordinate `Subgroup.LinearizingCoordinate.transFun`. It takes the quotient
coordinate of a point of the invariant disc in the first local linearizing coordinate to its
quotient coordinate in the second
(`Subgroup.LinearizingCoordinate.quotientCoordinateTrans_quotientCoordinate`), and it is
holomorphic on the set of quotient-coordinate values
(`Subgroup.LinearizingCoordinate.differentiableOn_quotientCoordinateTrans`). -/
def LinearizingCoordinate.quotientCoordinateTrans (ψ ψ' : Γ.LinearizingCoordinate z ε) : ℂ → ℂ :=
  TauCeti.descendPow (Nat.card (stabilizer Γ z))
    fun u : ℂ ↦ (transFun ψ ψ' u) ^ Nat.card (stabilizer Γ z)

/-- The transition of the local quotient coordinates is holomorphic on the set of
quotient-coordinate values of the first local linearizing coordinate: it is the descent of the
`m`-th power of a holomorphic function invariant under the rotations, by
`TauCeti.differentiableOn_descendPow`. -/
theorem LinearizingCoordinate.differentiableOn_quotientCoordinateTrans (hε : 0 < ε)
    (ψ ψ' : Γ.LinearizingCoordinate z ε) :
    DifferentiableOn ℂ (quotientCoordinateTrans ψ ψ') ψ.quotientImage := by
  refine TauCeti.differentiableOn_descendPow (ψ.isOpen_image hε) ?_ ?_
  · exact (differentiableOn_transFun ψ ψ').pow _
  · intro u hu ζ
    rw [transFun_smul ψ ψ' hu ζ, rootsOfUnity.smul_pow]

/-- **The transition of the local quotient coordinates takes a quotient coordinate to a quotient
coordinate**, so it relates the local quotient coordinates of the two local linearizing
coordinates. -/
@[simp]
theorem LinearizingCoordinate.quotientCoordinateTrans_quotientCoordinate
    (ψ ψ' : Γ.LinearizingCoordinate z ε) (τ : stabilizerBall Γ z ε) :
    quotientCoordinateTrans ψ ψ' (quotientCoordinate ψ τ) = quotientCoordinate ψ' τ := by
  have hζ : ∀ ζ : rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ,
      (transFun ψ ψ' (ζ • (coordinate ψ τ : ℂ))) ^ Nat.card (stabilizer Γ z)
        = (transFun ψ ψ' (coordinate ψ τ : ℂ)) ^ Nat.card (stabilizer Γ z) := by
    intro ζ
    rw [transFun_smul ψ ψ' ((ψ.mem_image_iff (coordinate ψ τ)).mpr ⟨τ, rfl⟩) ζ,
      rootsOfUnity.smul_pow]
  rw [quotientCoordinate, quotientCoordinateTrans, TauCeti.descendPow_pow hζ]
  simp only [transFun, coordinate, quotientCoordinate]
  rw [ψ.left_inv _ (mem_ball_discCoordinate τ)]

/-- **The transition of the local quotient coordinates takes a quotient coordinate to a quotient
coordinate**, so it maps the set of quotient-coordinate values of the first local linearizing
coordinate into that of the second. -/
theorem LinearizingCoordinate.quotientCoordinateTrans_mem_quotientImage
    (ψ ψ' : Γ.LinearizingCoordinate z ε) {w : ℂ} (hw : w ∈ ψ.quotientImage) :
    quotientCoordinateTrans ψ ψ' w ∈ ψ'.quotientImage := by
  obtain ⟨τ, rfl⟩ := (ψ.mem_quotientImage_iff w).mp hw
  exact (ψ'.mem_quotientImage_iff _).mpr
    ⟨τ, quotientCoordinateTrans_quotientCoordinate ψ ψ' τ⟩

/-- **The transitions of the local quotient coordinates in the two directions are inverse** on the
set of quotient-coordinate values: the transition
`Subgroup.LinearizingCoordinate.quotientCoordinateTrans ψ' ψ`, the transition in the other
direction, is the inverse of `Subgroup.LinearizingCoordinate.quotientCoordinateTrans ψ ψ'`, so
the transition is a biholomorphic change of the local quotient coordinate. -/
@[simp]
theorem LinearizingCoordinate.quotientCoordinateTrans_quotientCoordinateTrans
    (ψ ψ' : Γ.LinearizingCoordinate z ε) {w : ℂ} (hw : w ∈ ψ.quotientImage) :
    quotientCoordinateTrans ψ' ψ (quotientCoordinateTrans ψ ψ' w) = w := by
  obtain ⟨u, hu, rfl⟩ := hw
  have hf : ∀ ζ : rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ,
      (transFun ψ ψ' (ζ • (u : ℂ))) ^ Nat.card (stabilizer Γ z)
        = (transFun ψ ψ' (u : ℂ)) ^ Nat.card (stabilizer Γ z) := by
    intro ζ
    rw [transFun_smul ψ ψ' hu ζ, rootsOfUnity.smul_pow]
  have hfu : transFun ψ ψ' (u : ℂ) ∈ ψ'.image := transFun_mem_image ψ ψ' hu
  have hg : ∀ ζ : rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ,
      (transFun ψ' ψ (ζ • transFun ψ ψ' (u : ℂ))) ^ Nat.card (stabilizer Γ z)
        = (transFun ψ' ψ (transFun ψ ψ' (u : ℂ))) ^ Nat.card (stabilizer Γ z) := by
    intro ζ
    rw [transFun_smul ψ' ψ hfu ζ, rootsOfUnity.smul_pow]
  simp only [quotientCoordinateTrans]
  rw [TauCeti.descendPow_pow hf, TauCeti.descendPow_pow hg, transFun_transFun ψ ψ' hu]

/-- **The local quotient coordinates of two local linearizing coordinates are related by a
biholomorphic transition.** The local quotient coordinate of a local linearizing coordinate
`Subgroup.LinearizingCoordinate.quotientCoordinate` is a holomorphic function on the invariant
disc of radius `ε`, constant on the orbits of the stabilizer of `z`
(`Subgroup.LinearizingCoordinate.quotientCoordinate_smul`), with those orbits as its level sets
(`Subgroup.LinearizingCoordinate.quotientCoordinate_eq_iff`). Its values range over the open set
`Subgroup.LinearizingCoordinate.quotientImage` of quotient-coordinate values, and the quotient
coordinates of two local linearizing coordinates differ by a biholomorphic change of those open
sets: a holomorphic map `T` between the two open sets of quotient-coordinate values with a
holomorphic inverse `T'`, each taking the quotient-coordinate values of its own open set into the
other (`Subgroup.LinearizingCoordinate.quotientCoordinateTrans_mem_quotientImage`), and taking
the quotient coordinate of a point of the invariant disc in the first local linearizing coordinate
to its quotient coordinate in the second. The transition is
`Subgroup.LinearizingCoordinate.quotientCoordinateTrans`, the descent of the change of local
linearizing coordinate `Subgroup.LinearizingCoordinate.transFun` through `u ↦ u ^ m`. -/
theorem LinearizingCoordinate.exists_quotientCoordinate_trans (hε : 0 < ε)
    (ψ ψ' : Γ.LinearizingCoordinate z ε) :
    ∃ T T' : ℂ → ℂ,
      IsOpen ψ.quotientImage ∧ IsOpen ψ'.quotientImage ∧
      DifferentiableOn ℂ T ψ.quotientImage ∧
      DifferentiableOn ℂ T' ψ'.quotientImage ∧
      (∀ w ∈ ψ.quotientImage, T w ∈ ψ'.quotientImage) ∧
      (∀ w ∈ ψ'.quotientImage, T' w ∈ ψ.quotientImage) ∧
      (∀ τ : stabilizerBall Γ z ε, T (ψ.quotientCoordinate τ) = ψ'.quotientCoordinate τ) ∧
      (∀ τ : stabilizerBall Γ z ε, T' (ψ'.quotientCoordinate τ) = ψ.quotientCoordinate τ) ∧
      (∀ w ∈ ψ.quotientImage, (T' ∘ T) w = w) ∧
      (∀ w ∈ ψ'.quotientImage, (T ∘ T') w = w) :=
  ⟨LinearizingCoordinate.quotientCoordinateTrans ψ ψ',
    LinearizingCoordinate.quotientCoordinateTrans ψ' ψ,
    LinearizingCoordinate.isOpen_quotientImage hε ψ,
    LinearizingCoordinate.isOpen_quotientImage hε ψ',
    LinearizingCoordinate.differentiableOn_quotientCoordinateTrans hε ψ ψ',
    LinearizingCoordinate.differentiableOn_quotientCoordinateTrans hε ψ' ψ,
    fun _ hw => LinearizingCoordinate.quotientCoordinateTrans_mem_quotientImage ψ ψ' hw,
    fun _ hw => LinearizingCoordinate.quotientCoordinateTrans_mem_quotientImage ψ' ψ hw,
    fun _ => LinearizingCoordinate.quotientCoordinateTrans_quotientCoordinate ψ ψ' _,
    fun _ => LinearizingCoordinate.quotientCoordinateTrans_quotientCoordinate ψ' ψ _,
    fun _ hw =>
      LinearizingCoordinate.quotientCoordinateTrans_quotientCoordinateTrans ψ ψ' hw,
    fun _ hw =>
      LinearizingCoordinate.quotientCoordinateTrans_quotientCoordinateTrans ψ' ψ hw⟩

/-- **The disc coordinate centred at `z` is a local linearizing coordinate**: the reparametrization
by the disc coordinate itself, whose coordinate is the disc coordinate
`Subgroup.LinearizingCoordinate.coordinate` and whose quotient coordinate is
`discCoordinate z τ ^ Nat.card (stabilizer Γ z)`, the coordinate of
`Subgroup.stabilizerBallQuotientHomeomorph` and of the chart
`Subgroup.stabilizerBallQuotientChart`
(`Subgroup.LinearizingCoordinate.quotientCoordinate_discCoordinate`). -/
def LinearizingCoordinate.discCoordinate : Γ.LinearizingCoordinate z ε where
  toFun u := u
  invFun u := u
  image := Metric.ball 0 (Real.tanh (ε / 2))
  image_eq := by
    have h : (fun u => u) '' Metric.ball 0 (Real.tanh (ε / 2))
        = (id : ℂ → ℂ) '' Metric.ball 0 (Real.tanh (ε / 2)) := rfl
    rw [h, Set.image_id]
  differentiable := differentiable_id.differentiableOn
  differentiable_inv := differentiable_id.differentiableOn
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl
  zero := rfl
  toFun_eq_id := fun _ _ => rfl
  invFun_eq_id := fun _ _ => rfl
  smul := fun _ _ _ => rfl

/-- The coordinate in the disc coordinate of a local linearizing coordinate is the disc
coordinate itself. -/
@[simp]
theorem LinearizingCoordinate.coordinate_discCoordinate (τ : stabilizerBall Γ z ε) :
    coordinate (Γ := Γ) (z := z) (ε := ε) discCoordinate τ = UpperHalfPlane.discCoordinate z τ := by
  simp only [coordinate, LinearizingCoordinate.discCoordinate]

/-- The local quotient coordinate in the disc coordinate of a local linearizing coordinate is
the `Nat.card (stabilizer Γ z)`-th power of the disc coordinate, the coordinate of the chart
`Subgroup.stabilizerBallQuotientChart` on the coarse orbit quotient. -/
@[simp]
theorem LinearizingCoordinate.quotientCoordinate_discCoordinate (τ : stabilizerBall Γ z ε) :
    quotientCoordinate (Γ := Γ) (z := z) (ε := ε) discCoordinate τ
      = UpperHalfPlane.discCoordinate z τ ^ Nat.card (stabilizer Γ z) := by
  simp only [quotientCoordinate, coordinate_discCoordinate]

/-- **A local linearizing coordinate is determined by its reparametrization on the disc of the
invariant disc**: two local linearizing coordinates with the same reparametrization there agree
everywhere, the ambient reparametrizations being the identity outside that disc
(`Subgroup.LinearizingCoordinate.toFun_eq_id`), and so agree on the image, by
`Subgroup.LinearizingCoordinate.image_eq`; their inverse reparametrizations agree on the image,
being mutual inverses of the reparametrization there
(`Subgroup.LinearizingCoordinate.right_inv`), and are the identity outside it
(`Subgroup.LinearizingCoordinate.invFun_eq_id`). -/
@[ext]
theorem LinearizingCoordinate.ext {ε : ℝ} {z : ℍ} {Γ : Subgroup PSL(2, ℝ)}
    [Finite ↥(stabilizer Γ z)] {τ τ' : Γ.LinearizingCoordinate z ε}
    (hcoord : ∀ w : ℂ, w ∈ Metric.ball 0 (Real.tanh (ε / 2)) → τ.toFun w = τ'.toFun w) :
    τ = τ' := by
  have hto : τ.toFun = τ'.toFun := by
    funext w
    by_cases hw : w ∈ Metric.ball 0 (Real.tanh (ε / 2))
    · exact hcoord w hw
    · exact τ.toFun_eq_id w hw |>.trans (τ'.toFun_eq_id w hw).symm
  have himage : τ.image = τ'.image := by rw [τ.image_eq, τ'.image_eq, hto]
  have hin : τ.invFun = τ'.invFun := by
    funext w
    by_cases hw : w ∈ τ.image
    · obtain ⟨v, hv, hwv⟩ : ∃ v ∈ Metric.ball 0 (Real.tanh (ε / 2)), τ.toFun v = w := by
        rw [τ.image_eq] at hw
        exact hw
      have hwv' : τ'.toFun v = w := by simpa only [hto] using hwv
      calc τ.invFun w = τ.invFun (τ.toFun v) := by rw [hwv]
        _ = v := τ.left_inv v hv
        _ = τ'.invFun (τ'.toFun v) := (τ'.left_inv v hv).symm
        _ = τ'.invFun w := by rw [hwv']
    · have hw' : w ∉ τ'.image := by rw [← himage]; exact hw
      rw [τ.invFun_eq_id w hw]
      exact (τ'.invFun_eq_id w hw').symm
  cases τ
  cases τ'
  simp_all

open Classical in
/-- **A rotation of the disc coordinate is a local linearizing coordinate**: the reparametrization
of the disc of the invariant disc by a root of unity of order `Nat.card (stabilizer Γ z)`, whose
coordinate is the disc coordinate multiplied by that root of unity
(`Subgroup.LinearizingCoordinate.coordinate_rotation`). The quotient coordinate of a rotation is
the quotient coordinate of the disc coordinate itself
(`Subgroup.LinearizingCoordinate.quotientCoordinate_rotation`), the rotation being an `m`-th root
of unity. -/
def LinearizingCoordinate.rotation (ζ : rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ) :
    Γ.LinearizingCoordinate z ε where
  toFun u := if u ∈ Metric.ball 0 (Real.tanh (ε / 2)) then ζ • u else u
  invFun u := if u ∈ Metric.ball 0 (Real.tanh (ε / 2)) then ζ⁻¹ • u else u
  image := Metric.ball 0 (Real.tanh (ε / 2))
  image_eq := by
    have heq : (fun u : ℂ => if u ∈ Metric.ball 0 (Real.tanh (ε / 2)) then ζ • u else u) ''
        Metric.ball 0 (Real.tanh (ε / 2)) = Metric.ball 0 (Real.tanh (ε / 2)) := by
      rw [Set.ext_iff]
      intro w
      constructor
      · rintro ⟨u, hu, rfl⟩
        simp only [reduceIte, hu]
        exact mem_ball_smul ζ hu
      · intro hw
        refine ⟨ζ⁻¹ • w, mem_ball_smul (ζ := ζ⁻¹) hw, ?_⟩
        simp only [reduceIte, mem_ball_smul (ζ := ζ⁻¹) hw, smul_smul, mul_inv_cancel, one_smul]
    exact heq.symm
  -- on the disc the reparametrization is multiplication by `ζ`, or by `ζ⁻¹`, each a
  -- differentiable function of the point, so the reparametrization agrees there with a
  -- differentiable function and is differentiable there by `DifferentiableOn.congr_mono`
  differentiable := by
    have h : Differentiable ℂ (fun w : ℂ => ζ • w) := by fun_prop
    refine h.differentiableOn.congr_mono (fun u hu => ?_) (Set.subset_univ _)
    simp only [reduceIte, hu]
  differentiable_inv := by
    have h : Differentiable ℂ (fun w : ℂ => ζ⁻¹ • w) := by fun_prop
    refine h.differentiableOn.congr_mono (fun u hu => ?_) (Set.subset_univ _)
    simp only [reduceIte, hu]
  left_inv := by
    intro w hw
    simp only [reduceIte, hw, mem_ball_smul ζ hw, smul_smul, inv_mul_cancel, one_smul]
  right_inv := by
    intro w hw
    have hw' : w ∈ Metric.ball 0 (Real.tanh (ε / 2)) := hw
    simp only [reduceIte, hw', mem_ball_smul (ζ := ζ⁻¹) hw, smul_smul, mul_inv_cancel, one_smul]
  zero := by
    by_cases h : (0 : ℂ) ∈ Metric.ball 0 (Real.tanh (ε / 2)) <;> simp [h, smul_zero]
  toFun_eq_id := by
    intro w hw
    simp only [reduceIte, hw]
  invFun_eq_id := by
    intro w hw
    have hw' : w ∉ Metric.ball 0 (Real.tanh (ε / 2)) := hw
    simp only [reduceIte, hw']
  smul := by
    intro η w hw
    have hηw : ((η : ℂˣ) : ℂ) * w ∈ Metric.ball 0 (Real.tanh (ε / 2)) := by
      rw [← rootsOfUnity.smul_eq_mul]
      exact mem_ball_smul η hw
    simp only [rootsOfUnity.smul_eq_mul, reduceIte, hηw, hw]
    ac_rfl

/-- The coordinate in a rotation of the disc coordinate is the disc coordinate multiplied by
the root of unity of the rotation. -/
@[simp]
theorem LinearizingCoordinate.coordinate_rotation
    (ζ : rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ) (τ : stabilizerBall Γ z ε) :
    coordinate (Γ := Γ) (z := z) (ε := ε) (rotation ζ) τ
      = ζ • UpperHalfPlane.discCoordinate z (τ : ℍ) := by
  simp only [coordinate, LinearizingCoordinate.rotation, mem_ball_discCoordinate, reduceIte]

/-- The local quotient coordinate in a rotation of the disc coordinate is the local quotient
coordinate in the disc coordinate itself, the rotation being a `Nat.card (stabilizer Γ z)`-th
root of unity. -/
@[simp]
theorem LinearizingCoordinate.quotientCoordinate_rotation
    (ζ : rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ) (τ : stabilizerBall Γ z ε) :
    quotientCoordinate (Γ := Γ) (z := z) (ε := ε) (rotation ζ) τ
      = UpperHalfPlane.discCoordinate z τ ^ Nat.card (stabilizer Γ z) := by
  simp only [quotientCoordinate, coordinate_rotation, rootsOfUnity.smul_pow]

end Subgroup
