/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected
public import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Basic

/-!
# Local linearizing coordinates at a point of finite stabilizer

Let `Γ ≤ PSL(2, ℝ)` and let `z` be a point of the upper half-plane whose stabilizer has finite
order `m`. A **local linearizing coordinate** at `z` is a biholomorphic coordinate on the
invariant hyperbolic disc of positive radius `ε` about `z` which sends `z` to the centre and in
which the stabilizer of `z` acts by rotations: it is a biholomorphic reparametrization `ψ` of the
Euclidean disc of radius `tanh (ε / 2)`, the image of the invariant disc in the disc coordinate
centred at `z`, fixing `0` and intertwining the rotation action of the `m`-th roots of unity on
the disc with the rotation action on its image (`Subgroup.LinearizingCoordinate`). The stabilizer
of `z` acts on the invariant hyperbolic disc itself, and the disc coordinate centred at `z` turns
that action into the rotation action of the `m`-th roots of unity, so the rotation by which a
stabilizer element acts in a local linearizing coordinate is `Subgroup.stabilizerRotation` in
every one of them (`Subgroup.LinearizingCoordinate.coordinate_smul`).

A local linearizing coordinate is genuinely *local*: its image is its own open set, the
`target` of the partial equivalence `Subgroup.LinearizingCoordinate.toEquiv` of the
reparametrization, which is not required to be the whole unit disc, and the equivariant
biholomorphic reparametrizations of a disc are not all rotations. In particular
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
(`Subgroup.LinearizingCoordinate.quotientCoordinateTrans`, holomorphic on the first open set
(`Subgroup.LinearizingCoordinate.differentiableOn_quotientCoordinateTrans`) into the second
(`Subgroup.LinearizingCoordinate.quotientCoordinateTrans_mem_quotientImage`) and inverse to the
transition in the other direction
(`Subgroup.LinearizingCoordinate.quotientCoordinateTrans_quotientCoordinateTrans`)) — obtained by
descending the change of coordinate through `u ↦ u ^ m` with
`TauCeti.differentiableOn_descendPow`. Since the
rotation by which an element of the stabilizer acts is `Subgroup.stabilizerRotation`, the same
rotation appears in every local linearizing coordinate
(`Subgroup.LinearizingCoordinate.coordinate_smul`). The coordinate, and with it the local quotient
coordinate, is holomorphic on the invariant hyperbolic disc
(`Subgroup.LinearizingCoordinate.mdifferentiableOn_coordinate`,
`Subgroup.LinearizingCoordinate.mdifferentiableOn_quotientCoordinate`).

The two coordinates available by construction, for `0 < ε`, are the disc coordinate centred at `z`
and its rotation by a root of unity (`Subgroup.LinearizingCoordinate.discCoordinate`,
`Subgroup.LinearizingCoordinate.rotation`); for the disc coordinate the quotient coordinate is
`discCoordinate z τ ^ m`, the coordinate of `Subgroup.stabilizerBallQuotientHomeomorph` and
`Subgroup.stabilizerBallQuotientChart`, and a rotation leaves it unchanged
(`Subgroup.LinearizingCoordinate.quotientCoordinate_rotation`). Independence from the choice of
the invariant disc is `Subgroup.stabilizerBallQuotientChart_trans_apply`.

## Main declarations

* `Subgroup.LinearizingCoordinate`: a local biholomorphic coordinate linearizing the stabilizer
  of `z` on the invariant disc of radius `ε`, the positivity of which is stored in the structure
  as `Subgroup.LinearizingCoordinate.ε_pos`.
* `Subgroup.LinearizingCoordinate.coordinate`, `…_smul`, `…_injective` and
  `…_mdifferentiableOn_coordinate`: the coordinate of a point of the invariant disc, the action of
  the stabilizer on it, and its holomorphy on the invariant disc.
* `Subgroup.LinearizingCoordinate.toEquiv`, `…_isOpen_target`, `…_mem_target_iff`: the open image
  of the reparametrization, the set of coordinate values.
* `Subgroup.LinearizingCoordinate.transEquiv`, `…_transEquiv_coordinate`,
  `…_transEquiv_transEquiv` and `Subgroup.LinearizingCoordinate.differentiableOn_transEquiv`: the
  biholomorphic change of local linearizing coordinate between two local linearizing coordinates.
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

open scoped ComplexConjugate Manifold MatrixGroups

namespace Subgroup

variable {Γ : Subgroup PSL(2, ℝ)} {z : ℍ} {ε : ℝ} [Finite (stabilizer Γ z)]

/-- **A local linearizing coordinate** at `z` on the invariant hyperbolic disc of radius `ε`,
which is positive, that hypothesis being stored as
`Subgroup.LinearizingCoordinate.ε_pos` so that the disc is a neighbourhood of `z`: a
partial equivalence `toEquiv` of `ℂ` from the Euclidean disc of radius `Real.tanh (ε / 2)`, the
image of the invariant disc in the disc coordinate centred at `z`, to its own image, which fixes `0`
and intertwines the rotation action of the `Nat.card (stabilizer Γ z)`-th roots of unity on the disc
with the rotation action on that image. The coordinate of a point `τ` of the invariant disc is then
`Subgroup.LinearizingCoordinate.coordinate ψ τ = toEquiv (discCoordinate z τ)`, a biholomorphic
coordinate of the invariant disc; the stabilizer of `z` acts on that disc, and by
`Subgroup.LinearizingCoordinate.coordinate_smul` it acts in this coordinate by the rotation
`Subgroup.stabilizerRotation`, so the quotient by the stabilizer is the power map `u ↦ u ^ m`,
`m = Nat.card (stabilizer Γ z)`.

The `target` of the reparametrization, its image on that disc, is only required to be open, not to
be the whole Euclidean disc: local linearizing coordinates are not all rotations of the disc
coordinate, the equivariant biholomorphic reparametrizations of a disc being an infinite-dimensional
family. Biholomorphy is the requirement that `toFun` and `invFun` be holomorphic on the disc and on
the `target` respectively and inverse to one another there. Both holomorphy conditions are stored
explicitly, being hypotheses of the structure, so that the biholomorphic reparametrization is
available without deriving the holomorphy of the inverse from that of `toFun` by the holomorphic
inverse function theorem. The `target` is open by
`Subgroup.LinearizingCoordinate.isOpen_target`. -/
structure LinearizingCoordinate (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) (ε : ℝ)
    [Finite (stabilizer Γ z)] where
  /-- the radius of the invariant disc is positive, the invariant disc and its disc coordinate then
  being non-empty and containing the centre `z`, as a local coordinate about `z` is -/
  ε_pos : 0 < ε
  /-- the reparametrization of the disc coordinate, a partial equivalence of `ℂ` whose source is
  the disc of the invariant disc and whose target is its image -/
  toEquiv : PartialEquiv ℂ ℂ
  /-- the source of the reparametrization is the disc of the invariant disc -/
  toEquiv_source : toEquiv.source = Metric.ball 0 (Real.tanh (ε / 2))
  /-- the reparametrization is holomorphic on the disc of the invariant disc -/
  differentiableOn : DifferentiableOn ℂ toEquiv.toFun (Metric.ball 0 (Real.tanh (ε / 2)))
  /-- the inverse reparametrization is holomorphic on the image of the reparametrization -/
  differentiableOn_invFun : DifferentiableOn ℂ toEquiv.invFun toEquiv.target
  /-- the reparametrization fixes the centre -/
  map_zero : toEquiv.toFun 0 = 0
  /-- the reparametrization is the identity outside the disc of the invariant disc, the choice
  which leaves the disc coordinate the identity reparametrization; it makes a local linearizing
  coordinate determined by its values on that disc (`Subgroup.LinearizingCoordinate.ext`) -/
  toFun_eq_id : ∀ w : ℂ, w ∉ Metric.ball 0 (Real.tanh (ε / 2)) → toEquiv.toFun w = w
  /-- the inverse reparametrization is the identity outside the image of the reparametrization,
  so that it too is determined by the values of the reparametrization on the disc of the
  invariant disc (`Subgroup.LinearizingCoordinate.ext`) -/
  invFun_eq_id : ∀ w : ℂ, w ∉ toEquiv.target → toEquiv.invFun w = w
  /-- the reparametrization intertwines the rotation action of the roots of unity on the disc
  with the rotation action on its image -/
  map_smul : ∀ ζ : rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ, ∀ w : ℂ,
    w ∈ Metric.ball 0 (Real.tanh (ε / 2)) → toEquiv.toFun (ζ • w) = ζ • toEquiv.toFun w

omit [Finite (stabilizer Γ z)] in
/-- The disc coordinate of a point of the invariant disc lies in the disc of the invariant
disc, the domain of a reparametrization. -/
private theorem mem_ball_discCoordinate (τ : stabilizerBall Γ z ε) :
    discCoordinate z (τ : ℍ) ∈ Metric.ball 0 (Real.tanh (ε / 2)) := by
  have hball : (τ : ℍ) ∈ Metric.ball z ε := Metric.mem_ball.mpr ((mem_stabilizerBall Γ z ε).1 τ.2)
  rw [mem_ball_zero_iff]
  exact (mem_ball_iff_norm_discCoordinate_lt (z := z) (τ := (τ : ℍ)) (ε := ε)).mp hball

/-- A rotation of a point of the disc of the invariant disc lies in it, that disc being
`TauCeti.rootsOfUnityBall`, the invariant set of the `Nat.card (stabilizer Γ z)`-th roots of
unity. -/
private theorem mem_ball_smul (ζ : rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ) {w : ℂ}
    (hw : w ∈ Metric.ball 0 (Real.tanh (ε / 2))) :
    ζ • w ∈ Metric.ball 0 (Real.tanh (ε / 2)) := by
  have hζw := (TauCeti.rootsOfUnityBall (Nat.card (stabilizer Γ z))
    (Real.tanh (ε / 2))).smul_mem ζ (TauCeti.mem_rootsOfUnityBall.mpr
      (mem_ball_zero_iff.mp hw))
  exact mem_ball_zero_iff.mpr (TauCeti.mem_rootsOfUnityBall.mp hζw)

/-- The reparametrization of a local linearizing coordinate is injective on the disc of the
invariant disc, being a partial equivalence on its source. -/
theorem LinearizingCoordinate.toFun_injOn_ball (ψ : Γ.LinearizingCoordinate z ε) :
    Set.InjOn ψ.toEquiv (Metric.ball 0 (Real.tanh (ε / 2))) :=
  ψ.toEquiv_source ▸ ψ.toEquiv.injOn

/-- The inverse reparametrization of a local linearizing coordinate takes a point of the image
back into the disc of the invariant disc. -/
theorem LinearizingCoordinate.mem_ball_invFun (ψ : Γ.LinearizingCoordinate z ε)
    {u : ℂ} (hu : u ∈ ψ.toEquiv.target) :
    ψ.toEquiv.invFun u ∈ Metric.ball 0 (Real.tanh (ε / 2)) := by
  rw [← ψ.toEquiv_source]
  exact ψ.toEquiv.map_target hu

/-- **The coordinate of a point of the invariant disc in a local linearizing coordinate**: the
reparametrized disc coordinate, a biholomorphic coordinate on the invariant hyperbolic disc of
radius `ε` about `z` centred at `z` in which the stabilizer of `z` acts by its rotation
`Subgroup.stabilizerRotation`
(`Subgroup.LinearizingCoordinate.coordinate_smul`), holomorphic there by
`Subgroup.LinearizingCoordinate.mdifferentiableOn_coordinate`. -/
def LinearizingCoordinate.coordinate (ψ : Γ.LinearizingCoordinate z ε)
    (τ : stabilizerBall Γ z ε) : ℂ := ψ.toEquiv (discCoordinate z (τ : ℍ))

/-- A point of the invariant disc has coordinate `0` in a local linearizing coordinate exactly
when it is the centre: the coordinate is centred at the centre. -/
@[simp]
theorem LinearizingCoordinate.coordinate_eq_zero_iff
    (ψ : Γ.LinearizingCoordinate z ε) (τ : stabilizerBall Γ z ε) :
    coordinate ψ τ = 0 ↔ (τ : ℍ) = z := by
  have hε : 0 < ε := lt_of_le_of_lt dist_nonneg ((mem_stabilizerBall Γ z ε).1 τ.2)
  constructor
  · intro h
    have h' : ψ.toEquiv (discCoordinate z (τ : ℍ)) = ψ.toEquiv 0 := by
      have h'' : ψ.toEquiv (discCoordinate z (τ : ℍ)) = 0 := h
      rw [h'', ψ.map_zero]
    have hr : 0 < Real.tanh (ε / 2) := by
      rw [← Real.tanh_zero]; exact Real.tanh_strictMono (by linarith)
    have hinj : discCoordinate z (τ : ℍ) = 0 :=
      ψ.toFun_injOn_ball (mem_ball_discCoordinate τ)
        (Metric.mem_ball_self hr) h'
    exact discCoordinate_eq_zero_iff.mp hinj
  · intro hτ
    have hmem : (z : ℍ) ∈ (stabilizerBall Γ z ε : Set ℍ) :=
      (mem_stabilizerBall Γ z ε).2 (by rw [dist_self]; exact hε)
    have hτ' : τ = ⟨z, hmem⟩ := Subtype.ext hτ
    rw [hτ']
    simp only [coordinate, discCoordinate_self]
    exact ψ.map_zero

/-- The coordinate of a local linearizing coordinate is injective on the invariant disc. -/
theorem LinearizingCoordinate.coordinate_injective (ψ : Γ.LinearizingCoordinate z ε) :
    Function.Injective (coordinate ψ) :=
  fun _ _ h => Subtype.ext (discCoordinate_injective z
    (ψ.toFun_injOn_ball (mem_ball_discCoordinate _) (mem_ball_discCoordinate _) h))

/-- **The stabilizer of `z` acts in the coordinate of a local linearizing coordinate by its
rotation.** The rotation does not depend on the local linearizing coordinate: it is
`Subgroup.stabilizerRotation Γ z q`, the derivative of `q` at `z`. -/
@[simp]
theorem LinearizingCoordinate.coordinate_smul (ψ : Γ.LinearizingCoordinate z ε)
    (q : stabilizer Γ z) (τ : stabilizerBall Γ z ε) :
    coordinate ψ (q • τ) = ((stabilizerRotation Γ z q : ℂˣ) : ℂ) * coordinate ψ τ := by
  have hcoord : discCoordinate z ((q • τ : stabilizerBall Γ z ε) : ℍ)
      = ((stabilizerRotation Γ z q : ℂˣ) : ℂ) * discCoordinate z (τ : ℍ) := by
    rw [SubMulAction.val_smul, discCoordinate_smul_eq_rotation_smul, rootsOfUnity.smul_eq_mul,
      coe_stabilizerRotation]
  have hsmul : ψ.toEquiv (((stabilizerRotation Γ z q) • (discCoordinate z (τ : ℍ))) : ℂ)
      = stabilizerRotation Γ z q • ψ.toEquiv (discCoordinate z (τ : ℍ)) :=
    ψ.map_smul (stabilizerRotation Γ z q) (discCoordinate z (τ : ℍ)) (mem_ball_discCoordinate τ)
  simp only [coordinate]
  rw [hcoord]
  calc ψ.toEquiv (((stabilizerRotation Γ z q) • (discCoordinate z (τ : ℍ))) : ℂ)
      = stabilizerRotation Γ z q • ψ.toEquiv (discCoordinate z (τ : ℍ)) := hsmul
    _ = ((stabilizerRotation Γ z q : ℂˣ) : ℂ) * ψ.toEquiv (discCoordinate z (τ : ℍ)) :=
      rootsOfUnity.smul_eq_mul (stabilizerRotation Γ z q) (ψ.toEquiv (discCoordinate z (τ : ℍ)))
    _ = ((stabilizerRotation Γ z q : ℂˣ) : ℂ) * coordinate ψ τ := rfl

/-- **A point is a coordinate value of a local linearizing coordinate** exactly when it lies in
the `target` of the reparametrization, its image on the disc of the invariant disc. -/
@[simp]
theorem LinearizingCoordinate.mem_target_iff (ψ : Γ.LinearizingCoordinate z ε) (u : ℂ) :
    u ∈ ψ.toEquiv.target ↔ ∃ τ : stabilizerBall Γ z ε, u = coordinate ψ τ := by
  constructor
  · intro hu
    obtain ⟨w, hw, hwu⟩ := ψ.toEquiv.surjOn hu
    rw [ψ.toEquiv_source] at hw
    have hmem : w ∈ discCoordinate z '' Metric.ball z ε := by
      rw [UpperHalfPlane.image_discCoordinate_ball]
      exact hw
    obtain ⟨τ, hτ, hdt⟩ := (Set.mem_image (discCoordinate z) (Metric.ball z ε) w).mp hmem
    refine ⟨⟨τ, (mem_stabilizerBall Γ z ε).2 hτ⟩, ?_⟩
    simp only [coordinate]
    rw [hdt]
    exact hwu.symm
  · rintro ⟨τ, rfl⟩
    exact ψ.toEquiv.map_source (by rw [ψ.toEquiv_source]; exact mem_ball_discCoordinate τ)

/-- **The `target` of a local linearizing coordinate is open**: it is the image of the disc of
the invariant disc, an open set, under the reparametrization, which is holomorphic and injective
there (`TauCeti.isOpen_image_of_differentiableOn_of_injOn`). -/
theorem LinearizingCoordinate.isOpen_target (ψ : Γ.LinearizingCoordinate z ε) :
    IsOpen ψ.toEquiv.target := by
  rw [← ψ.toEquiv.image_source_eq_target, ψ.toEquiv_source]
  exact TauCeti.isOpen_image_of_differentiableOn_of_injOn Metric.isOpen_ball ψ.differentiableOn
    ψ.toFun_injOn_ball

/-- **The coordinate of a local linearizing coordinate is holomorphic on the invariant disc**:
on the ambient upper half-plane, the invariant disc being the ball `Metric.ball z ε`
(`Subgroup.mem_stabilizerBall`), it is the composition of the disc coordinate, which is holomorphic
by `UpperHalfPlane.mdifferentiable_discCoordinate`, with the reparametrization
`Subgroup.LinearizingCoordinate.differentiableOn`, which is holomorphic on the disc of the invariant
disc and which the disc coordinate maps the invariant disc into. Restricted to
`Subgroup.stabilizerBall Γ z ε` that composition is
`Subgroup.LinearizingCoordinate.coordinate`, so this is the holomorphy of that coordinate. -/
theorem LinearizingCoordinate.mdifferentiableOn_coordinate (ψ : Γ.LinearizingCoordinate z ε) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ ↦ ψ.toEquiv (discCoordinate z τ))
      (Metric.ball z ε) := by
  refine fun τ hτ => ?_
  have hτball : (τ : ℍ) ∈ stabilizerBall Γ z ε :=
    (mem_stabilizerBall Γ z ε).2 (mem_ball.1 hτ)
  have hMD : MDiffAt (fun σ : ℍ ↦ ψ.toEquiv (discCoordinate z σ)) τ := by
    refine UpperHalfPlane.mdifferentiableAt_iff.mpr ?_
    -- the disc coordinate is holomorphic at `τ`
    have hdisc : DifferentiableAt ℂ (discCoordinate z ∘ ofComplex) (τ : ℂ) :=
      UpperHalfPlane.mdifferentiableAt_iff.mp ((mdifferentiable_discCoordinate z) τ)
    -- the reparametrization is holomorphic at the disc coordinate of `τ`, which lies in its domain
    have hψ : DifferentiableAt ℂ ψ.toEquiv (discCoordinate z (ofComplex (τ : ℂ))) := by
      rw [ofComplex_apply]
      exact ψ.differentiableOn.differentiableAt
        (Metric.isOpen_ball.mem_nhds (mem_ball_discCoordinate ⟨τ, hτball⟩))
    have h : DifferentiableAt ℂ (fun w : ℂ ↦ ψ.toEquiv (discCoordinate z (ofComplex w))) (τ : ℂ) :=
      DifferentiableAt.comp (g := ψ.toEquiv) (f := discCoordinate z ∘ ofComplex) (x := τ) hψ hdisc
    simpa only [Function.comp_def] using h
  exact hMD.mdifferentiableWithinAt

/-- **The local quotient coordinate** in a local linearizing coordinate: the
`Nat.card (stabilizer Γ z)`-th power of the coordinate, the model of the quotient of the
invariant disc by the stabilizer of `z`, `m = Nat.card (stabilizer Γ z)`. Its level sets are the
orbits of that stabilizer (`Subgroup.LinearizingCoordinate.quotientCoordinate_eq_iff`), so it is a
coordinate on that quotient, and it is independent of the local linearizing coordinate up to the
biholomorphic transition
`Subgroup.LinearizingCoordinate.quotientCoordinateTrans`, holomorphic there by
`Subgroup.LinearizingCoordinate.differentiableOn_quotientCoordinateTrans`. -/
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
power, `m = Nat.card (stabilizer Γ z)`, of the `target` of the reparametrization, that is of its
image, and is an open set by
`Subgroup.LinearizingCoordinate.isOpen_quotientImage`. -/
def LinearizingCoordinate.quotientImage (ψ : Γ.LinearizingCoordinate z ε) : Set ℂ :=
  (· ^ Nat.card (stabilizer Γ z)) '' ψ.toEquiv.target

/-- **A point is a quotient-coordinate value of a local linearizing coordinate** exactly when it
is the `Nat.card (stabilizer Γ z)`-th power of a coordinate value. -/
@[simp]
theorem LinearizingCoordinate.mem_quotientImage_iff (ψ : Γ.LinearizingCoordinate z ε) (w : ℂ) :
    w ∈ ψ.quotientImage ↔ ∃ τ : stabilizerBall Γ z ε, w = quotientCoordinate ψ τ := by
  constructor
  · intro hw
    rw [quotientImage, Set.mem_image] at hw
    obtain ⟨u, hu, hw⟩ := hw
    obtain ⟨τ, rfl⟩ := (ψ.mem_target_iff u).mp hu
    refine ⟨τ, ?_⟩
    simpa only [quotientCoordinate] using hw.symm
  · rintro ⟨τ, rfl⟩
    rw [quotientImage, Set.mem_image]
    exact ⟨coordinate ψ τ, (ψ.mem_target_iff (coordinate ψ τ)).mpr ⟨τ, rfl⟩, rfl⟩

/-- **The set of quotient-coordinate values of a local linearizing coordinate is open**: it is the
image of the open `target` of the reparametrization under the power map `u ↦ u ^ m`, which is an
open map, being a non-constant holomorphic map (`Complex.isOpenQuotientMap_pow`). -/
theorem LinearizingCoordinate.isOpen_quotientImage (ψ : Γ.LinearizingCoordinate z ε) :
    IsOpen ψ.quotientImage := by
  rw [quotientImage]
  exact (Complex.isOpenQuotientMap_pow (Nat.card (stabilizer Γ z))).isOpenMap _ ψ.isOpen_target

/-- **The local quotient coordinate of a local linearizing coordinate is holomorphic on the
invariant disc**: it is the `Nat.card (stabilizer Γ z)`-th power of the holomorphic coordinate
`Subgroup.LinearizingCoordinate.mdifferentiableOn_coordinate`. On
`Subgroup.stabilizerBall Γ z ε` it is `Subgroup.LinearizingCoordinate.quotientCoordinate`, so this
is the holomorphy of the local quotient coordinate. -/
theorem LinearizingCoordinate.mdifferentiableOn_quotientCoordinate
    (ψ : Γ.LinearizingCoordinate z ε) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      (fun τ : ℍ ↦ (ψ.toEquiv (discCoordinate z τ)) ^ Nat.card (stabilizer Γ z))
      (Metric.ball z ε) :=
  -- the local quotient coordinate is the `Nat.card (stabilizer Γ z)`-th power of the coordinate
  fun τ hτ => (mdifferentiableOn_coordinate ψ τ hτ).pow _

/-- **The change of local linearizing coordinate** between two local linearizing coordinates on
the invariant disc: the partial equivalence `ψ.toEquiv.symm.trans ψ'.toEquiv`, the reparametrization
`ψ'` pulled back by the inverse reparametrization `ψ`, whose source is the `target` of `ψ` and whose
target is the `target` of `ψ'`
(`Subgroup.LinearizingCoordinate.transEquiv_source`,
`Subgroup.LinearizingCoordinate.transEquiv_target`). On the `target` of `ψ` it is a biholomorphism
onto the `target` of `ψ'` intertwining the rotation action
(`Subgroup.LinearizingCoordinate.transEquiv_smul`), taking a coordinate value to the
corresponding coordinate value
(`Subgroup.LinearizingCoordinate.transEquiv_coordinate`), and its inverse being the change of
coordinate in the other direction
(`Subgroup.LinearizingCoordinate.transEquiv_transEquiv`). -/
def LinearizingCoordinate.transEquiv (ψ ψ' : Γ.LinearizingCoordinate z ε) : PartialEquiv ℂ ℂ :=
  ψ.toEquiv.symm.trans ψ'.toEquiv

/-- The source of the change of local linearizing coordinate is the `target` of `ψ`, its image on
the disc of the invariant disc. -/
@[simp]
theorem LinearizingCoordinate.transEquiv_source (ψ ψ' : Γ.LinearizingCoordinate z ε) :
    (transEquiv ψ ψ').source = ψ.toEquiv.target := by
  simp only [transEquiv, PartialEquiv.trans_source'']
  rw [PartialEquiv.symm_symm, PartialEquiv.symm_target,
    ψ.toEquiv_source, ψ'.toEquiv_source, inter_self, ← ψ.toEquiv.image_source_eq_target,
    ← ψ.toEquiv_source]

/-- The target of the change of local linearizing coordinate is the `target` of `ψ'`, its image on
the disc of the invariant disc. -/
@[simp]
theorem LinearizingCoordinate.transEquiv_target (ψ ψ' : Γ.LinearizingCoordinate z ε) :
    (transEquiv ψ ψ').target = ψ'.toEquiv.target := by
  simp only [transEquiv, PartialEquiv.trans_target'']
  rw [PartialEquiv.symm_target, ψ'.toEquiv_source,
    ψ.toEquiv_source, inter_self, ← ψ'.toEquiv.image_source_eq_target, ← ψ'.toEquiv_source]

/-- **The change of local linearizing coordinate takes a coordinate value to a coordinate
value**: it carries a point of the `target` of `ψ` to a point of the `target` of `ψ'`, so the
change of coordinate is a map between the two open sets of coordinate values. -/
theorem LinearizingCoordinate.transEquiv_mem_target (ψ ψ' : Γ.LinearizingCoordinate z ε)
    {u : ℂ} (hu : u ∈ ψ.toEquiv.target) : transEquiv ψ ψ' u ∈ ψ'.toEquiv.target := by
  rw [← transEquiv_target]
  exact (transEquiv ψ ψ').map_source (by rw [transEquiv_source]; exact hu)

/-- **The change of local linearizing coordinate takes a coordinate value to a coordinate
value**, which is how a point of the invariant disc is read in the second local linearizing
coordinate once it is read in the first one. -/
@[simp]
theorem LinearizingCoordinate.transEquiv_coordinate (ψ ψ' : Γ.LinearizingCoordinate z ε)
    (τ : stabilizerBall Γ z ε) :
    transEquiv ψ ψ' (coordinate ψ τ) = coordinate ψ' τ := by
  simp only [transEquiv, coordinate, PartialEquiv.coe_trans, Function.comp_def]
  rw [ψ.toEquiv.left_inv (by rw [ψ.toEquiv_source]; exact mem_ball_discCoordinate τ)]

/-- **The inverse reparametrization of a local linearizing coordinate is equivariant for the
rotations**: it intertwines the rotation action of the roots of unity on the image with the
rotation action of the roots of unity on the disc. -/
theorem LinearizingCoordinate.invFun_smul (ψ : Γ.LinearizingCoordinate z ε) {u : ℂ}
    (hu : u ∈ ψ.toEquiv.target) (ζ : rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ) :
    ψ.toEquiv.invFun (ζ • u) = ζ • ψ.toEquiv.invFun u := by
  have hw := ψ.mem_ball_invFun hu
  have hwu : ψ.toEquiv.toFun (ζ • ψ.toEquiv.invFun u) = ζ • u := by
    rw [ψ.map_smul ζ _ hw]
    exact congrArg (fun w : ℂ => ζ • w) (ψ.toEquiv.right_inv hu)
  calc ψ.toEquiv.invFun (ζ • u)
      = ψ.toEquiv.invFun (ψ.toEquiv.toFun (ζ • ψ.toEquiv.invFun u)) := by rw [hwu]
    _ = ζ • ψ.toEquiv.invFun u :=
      ψ.toEquiv.left_inv (by rw [ψ.toEquiv_source]; exact mem_ball_smul ζ hw)

/-- The change of local linearizing coordinate intertwines the rotation action, being the pullback
of an equivariant reparametrization by an equivariant inverse. -/
@[simp]
theorem LinearizingCoordinate.transEquiv_smul (ψ ψ' : Γ.LinearizingCoordinate z ε) {u : ℂ}
    (hu : u ∈ ψ.toEquiv.target) (ζ : rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ) :
    transEquiv ψ ψ' (ζ • u) = ζ • transEquiv ψ ψ' u := by
  simp only [transEquiv, PartialEquiv.coe_trans, Function.comp_def]
  have hkey : ψ.toEquiv.invFun (ζ • u) = ζ • ψ.toEquiv.invFun u := ψ.invFun_smul hu ζ
  exact (congrArg (fun w : ℂ => ψ'.toEquiv.toFun w) hkey).trans
    (ψ'.map_smul ζ _ (ψ.mem_ball_invFun hu))

/-- The changes of local linearizing coordinate in the two directions are inverse: the change of
coordinate is a biholomorphism of the targets of the reparametrizations, being the `symm` of
itself. -/
@[simp]
theorem LinearizingCoordinate.transEquiv_transEquiv (ψ ψ' : Γ.LinearizingCoordinate z ε)
    {u : ℂ} (hu : u ∈ ψ.toEquiv.target) : transEquiv ψ' ψ (transEquiv ψ ψ' u) = u := by
  refine (transEquiv ψ ψ').left_inv ?_
  rw [transEquiv_source]
  exact hu

/-- The change of local linearizing coordinate is holomorphic on the `target` of the
reparametrization, being the composition of the inverse reparametrization, holomorphic there, with
the reparametrization, holomorphic on the disc of the invariant disc. -/
theorem LinearizingCoordinate.differentiableOn_transEquiv
    (ψ ψ' : Γ.LinearizingCoordinate z ε) :
    DifferentiableOn ℂ (transEquiv ψ ψ') ψ.toEquiv.target :=
  ψ'.differentiableOn.comp ψ.differentiableOn_invFun (fun _ hu => ψ.mem_ball_invFun hu)

/-- **The transition of the local quotient coordinates** of two local linearizing coordinates: the
descent through `u ↦ u ^ m`, `m = Nat.card (stabilizer Γ z)`, of the `m`-th power of the change of
local linearizing coordinate `Subgroup.LinearizingCoordinate.transEquiv`. It takes the quotient
coordinate of a point of the invariant disc in the first local linearizing coordinate to its
quotient coordinate in the second
(`Subgroup.LinearizingCoordinate.quotientCoordinateTrans_quotientCoordinate`), and it is
holomorphic on the set of quotient-coordinate values
(`Subgroup.LinearizingCoordinate.differentiableOn_quotientCoordinateTrans`). -/
def LinearizingCoordinate.quotientCoordinateTrans (ψ ψ' : Γ.LinearizingCoordinate z ε) : ℂ → ℂ :=
  TauCeti.descendPow (Nat.card (stabilizer Γ z))
    fun u : ℂ ↦ (transEquiv ψ ψ' u) ^ Nat.card (stabilizer Γ z)

/-- The transition of the local quotient coordinates is holomorphic on the set of
quotient-coordinate values of the first local linearizing coordinate: it is the descent of the
`m`-th power of a holomorphic function invariant under the rotations, by
`TauCeti.differentiableOn_descendPow`. -/
theorem LinearizingCoordinate.differentiableOn_quotientCoordinateTrans
    (ψ ψ' : Γ.LinearizingCoordinate z ε) :
    DifferentiableOn ℂ (quotientCoordinateTrans ψ ψ') ψ.quotientImage := by
  refine TauCeti.differentiableOn_descendPow ψ.isOpen_target ?_ ?_
  · exact (differentiableOn_transEquiv ψ ψ').pow _
  · intro u hu ζ
    rw [transEquiv_smul ψ ψ' hu ζ, rootsOfUnity.smul_pow]

/-- **The transition of the local quotient coordinates takes a quotient coordinate to a quotient
coordinate**, so it relates the local quotient coordinates of the two local linearizing
coordinates. -/
@[simp]
theorem LinearizingCoordinate.quotientCoordinateTrans_quotientCoordinate
    (ψ ψ' : Γ.LinearizingCoordinate z ε) (τ : stabilizerBall Γ z ε) :
    quotientCoordinateTrans ψ ψ' (quotientCoordinate ψ τ) = quotientCoordinate ψ' τ := by
  have hζ : ∀ ζ : rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ,
      (transEquiv ψ ψ' (ζ • (coordinate ψ τ : ℂ))) ^ Nat.card (stabilizer Γ z)
        = (transEquiv ψ ψ' (coordinate ψ τ : ℂ)) ^ Nat.card (stabilizer Γ z) := by
    intro ζ
    rw [transEquiv_smul ψ ψ' ((ψ.mem_target_iff (coordinate ψ τ)).mpr ⟨τ, rfl⟩) ζ,
      rootsOfUnity.smul_pow]
  rw [quotientCoordinate, quotientCoordinateTrans, TauCeti.descendPow_pow hζ]
  simp only [transEquiv, coordinate, quotientCoordinate, PartialEquiv.coe_trans,
    Function.comp_def]
  rw [ψ.toEquiv.left_inv (by rw [ψ.toEquiv_source]; exact mem_ball_discCoordinate τ)]

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
  obtain ⟨τ, rfl⟩ := (ψ.mem_quotientImage_iff w).mp hw
  simp

/-- **The disc coordinate centred at `z` is a local linearizing coordinate** on the invariant disc
of radius `ε > 0`: the reparametrization by the disc coordinate itself, whose coordinate is the
disc coordinate `Subgroup.LinearizingCoordinate.coordinate` and whose quotient coordinate is
`discCoordinate z τ ^ Nat.card (stabilizer Γ z)`, the coordinate of
`Subgroup.stabilizerBallQuotientHomeomorph` and of the chart
`Subgroup.stabilizerBallQuotientChart`
(`Subgroup.LinearizingCoordinate.quotientCoordinate_discCoordinate`). -/
def LinearizingCoordinate.discCoordinate (hε : 0 < ε) : Γ.LinearizingCoordinate z ε where
  ε_pos := hε
  toEquiv := PartialEquiv.ofSet (Metric.ball 0 (Real.tanh (ε / 2)))
  toEquiv_source := rfl
  differentiableOn := differentiable_id.differentiableOn
  differentiableOn_invFun := differentiable_id.differentiableOn
  map_zero := rfl
  toFun_eq_id := fun _ _ => rfl
  invFun_eq_id := fun _ _ => rfl
  map_smul := fun _ _ _ => rfl

/-- The coordinate in the disc coordinate of a local linearizing coordinate is the disc
coordinate itself. -/
@[simp]
theorem LinearizingCoordinate.coordinate_discCoordinate (hε : 0 < ε)
    (τ : stabilizerBall Γ z ε) :
    coordinate (Γ := Γ) (z := z) (ε := ε) (discCoordinate hε) τ
      = UpperHalfPlane.discCoordinate z τ := by
  simp only [coordinate, LinearizingCoordinate.discCoordinate, PartialEquiv.ofSet_coe, id]

/-- The local quotient coordinate in the disc coordinate of a local linearizing coordinate is
the `Nat.card (stabilizer Γ z)`-th power of the disc coordinate, the coordinate of the chart
`Subgroup.stabilizerBallQuotientChart` on the coarse orbit quotient. -/
@[simp]
theorem LinearizingCoordinate.quotientCoordinate_discCoordinate (hε : 0 < ε)
    (τ : stabilizerBall Γ z ε) :
    quotientCoordinate (Γ := Γ) (z := z) (ε := ε) (discCoordinate hε) τ
      = UpperHalfPlane.discCoordinate z τ ^ Nat.card (stabilizer Γ z) := by
  simp only [quotientCoordinate, coordinate_discCoordinate]

/-- **A local linearizing coordinate is determined by its reparametrization on the disc of the
invariant disc**: two local linearizing coordinates with the same reparametrization there agree
everywhere, the ambient reparametrizations being the identity outside that disc
(`Subgroup.LinearizingCoordinate.toFun_eq_id`), and so have the same `target`, being the image
of the disc of the invariant disc; their inverse reparametrizations agree on the `target`, being
mutual inverses of the reparametrization there
(`PartialEquiv.right_inv`), and are the identity outside it
(`Subgroup.LinearizingCoordinate.invFun_eq_id`). -/
@[ext]
theorem LinearizingCoordinate.ext {ε : ℝ} {z : ℍ} {Γ : Subgroup PSL(2, ℝ)}
    [Finite ↥(stabilizer Γ z)] {τ τ' : Γ.LinearizingCoordinate z ε}
    (hcoord : ∀ w : ℂ, w ∈ Metric.ball 0 (Real.tanh (ε / 2)) → τ.toEquiv w = τ'.toEquiv w) :
    τ = τ' := by
  have hto : (τ.toEquiv : ℂ → ℂ) = (τ'.toEquiv : ℂ → ℂ) := by
    funext w
    by_cases hw : w ∈ Metric.ball 0 (Real.tanh (ε / 2))
    · exact hcoord w hw
    · exact τ.toFun_eq_id w hw |>.trans (τ'.toFun_eq_id w hw).symm
  have htgt : τ.toEquiv.target = τ'.toEquiv.target := by
    calc τ.toEquiv.target = τ.toEquiv '' Metric.ball 0 (Real.tanh (ε / 2)) := by
          rw [← τ.toEquiv.image_source_eq_target, τ.toEquiv_source]
      _ = τ'.toEquiv '' Metric.ball 0 (Real.tanh (ε / 2)) := by rw [hto]
      _ = τ'.toEquiv.target := by
          rw [← τ'.toEquiv.image_source_eq_target, ← τ'.toEquiv_source]
  have hin : (τ.toEquiv.invFun : ℂ → ℂ) = (τ'.toEquiv.invFun : ℂ → ℂ) := by
    funext w
    by_cases hw : w ∈ τ.toEquiv.target
    · obtain ⟨v, hv, hwv⟩ : ∃ v ∈ Metric.ball 0 (Real.tanh (ε / 2)), τ.toEquiv v = w := by
        rw [← τ.toEquiv.image_source_eq_target, τ.toEquiv_source] at hw
        exact (Set.mem_image τ.toEquiv.toFun (Metric.ball 0 (Real.tanh (ε / 2))) w).mp hw
      have hwv' : τ'.toEquiv v = w := by simpa only [hto] using hwv
      calc τ.toEquiv.invFun w = τ.toEquiv.invFun (τ.toEquiv v) := by rw [hwv]
        _ = v := τ.toEquiv.left_inv (τ.toEquiv_source.symm ▸ hv)
        _ = τ'.toEquiv.invFun (τ'.toEquiv v) :=
          (τ'.toEquiv.left_inv (τ'.toEquiv_source.symm ▸ hv)).symm
        _ = τ'.toEquiv.invFun w := by rw [hwv']
    · have hw' : w ∉ τ'.toEquiv.target := by rw [← htgt]; exact hw
      rw [τ.invFun_eq_id w hw]
      exact (τ'.invFun_eq_id w hw').symm
  have heq : τ.toEquiv = τ'.toEquiv :=
    PartialEquiv.ext (congrFun hto) (congrFun hin)
      (by rw [τ.toEquiv_source, τ'.toEquiv_source])
  cases τ
  cases τ'
  simp_all

open Classical in
/-- **A rotation of the disc coordinate is a local linearizing coordinate** on the invariant disc
of radius `ε > 0`: the reparametrization of the disc of the invariant disc by a root of unity of
order `Nat.card (stabilizer Γ z)`, whose coordinate is the disc coordinate multiplied by that root
of unity
(`Subgroup.LinearizingCoordinate.coordinate_rotation`). The quotient coordinate of a rotation is
the quotient coordinate of the disc coordinate itself
(`Subgroup.LinearizingCoordinate.quotientCoordinate_rotation`), the rotation being an `m`-th root
of unity. -/
def LinearizingCoordinate.rotation (hε : 0 < ε) (ζ : rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ) :
    Γ.LinearizingCoordinate z ε where
  ε_pos := hε
  toEquiv :=
    { toFun := fun u : ℂ =>
        if u ∈ Metric.ball 0 (Real.tanh (ε / 2)) then ζ • u else u
      invFun := fun u : ℂ =>
        if u ∈ Metric.ball 0 (Real.tanh (ε / 2)) then ζ⁻¹ • u else u
      source := Metric.ball 0 (Real.tanh (ε / 2))
      target := Metric.ball 0 (Real.tanh (ε / 2))
      map_source' := by
        intro u hu
        simp only [reduceIte, hu]
        exact mem_ball_smul ζ hu
      map_target' := by
        intro u hu
        simp only [reduceIte, hu]
        exact mem_ball_smul (ζ := ζ⁻¹) hu
      left_inv' := by
        intro u hu
        simp only [reduceIte, hu, mem_ball_smul ζ hu, smul_smul, inv_mul_cancel, one_smul]
      right_inv' := by
        intro u hu
        simp only [reduceIte, hu, mem_ball_smul (ζ := ζ⁻¹) hu, smul_smul, mul_inv_cancel,
          one_smul] }
  toEquiv_source := rfl
  -- on the disc the reparametrization is multiplication by `ζ`, or by `ζ⁻¹`, each a
  -- differentiable function of the point, so the reparametrization agrees there with a
  -- differentiable function and is differentiable there by `DifferentiableOn.congr_mono`
  differentiableOn := by
    have h : Differentiable ℂ (fun w : ℂ => ζ • w) := by fun_prop
    refine h.differentiableOn.congr_mono (fun u hu => ?_) (Set.subset_univ _)
    simp only [reduceIte, hu]
  differentiableOn_invFun := by
    have h : Differentiable ℂ (fun w : ℂ => ζ⁻¹ • w) := by fun_prop
    refine h.differentiableOn.congr_mono (fun u hu => ?_) (Set.subset_univ _)
    simp only [reduceIte, hu]
  map_zero := by
    by_cases h : (0 : ℂ) ∈ Metric.ball 0 (Real.tanh (ε / 2)) <;> simp [h, smul_zero]
  toFun_eq_id := by
    intro w hw
    simp only [reduceIte, hw]
  invFun_eq_id := by
    intro w hw
    simp only [reduceIte, hw]
  map_smul := by
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
    (hε : 0 < ε) (ζ : rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ)
    (τ : stabilizerBall Γ z ε) :
    coordinate (Γ := Γ) (z := z) (ε := ε) (rotation hε ζ) τ
      = ζ • UpperHalfPlane.discCoordinate z (τ : ℍ) := by
  simp only [coordinate, LinearizingCoordinate.rotation, mem_ball_discCoordinate, reduceIte]

/-- The local quotient coordinate in a rotation of the disc coordinate is the local quotient
coordinate in the disc coordinate itself, the rotation being a `Nat.card (stabilizer Γ z)`-th
root of unity. -/
@[simp]
theorem LinearizingCoordinate.quotientCoordinate_rotation
    (hε : 0 < ε) (ζ : rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ)
    (τ : stabilizerBall Γ z ε) :
    quotientCoordinate (Γ := Γ) (z := z) (ε := ε) (rotation hε ζ) τ
      = UpperHalfPlane.discCoordinate z τ ^ Nat.card (stabilizer Γ z) := by
  simp only [quotientCoordinate, coordinate_rotation, rootsOfUnity.smul_pow]

end Subgroup
