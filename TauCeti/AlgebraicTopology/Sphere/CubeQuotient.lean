/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Homeomorph.Quotient
public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.Topology.Homotopy.Cube.Basic
public import TauCeti.Topology.Homotopy.HomotopyGroup.HomotopyEquiv
public import TauCeti.Topology.Homotopy.HomotopyGroup.Map
public import TauCeti.Topology.Homotopy.Homotopic.Rel

/-!
# The cube modulo its boundary is a sphere

Mathlib's homotopy groups `π_ n X x` are built from generalized loops, maps `I^n → X` sending the
boundary of the cube to `x`.  The classical description of `πₙ(X, x)` is by pointed maps
`(Sⁿ, s₀) → (X, x)` from the sphere, and the two are related by the homeomorphism
`Iⁿ / ∂Iⁿ ≅ Sⁿ`.  This file constructs that homeomorphism, for the unit sphere of
`EuclideanSpace ℝ (Fin (n + 1))` pointed at its north pole `e_last`, and transfers generalized
loops, their homotopies and their homotopy classes to pointed maps out of the sphere.

The map from the Euclidean closed unit ball of `ℝⁿ` to the unit sphere of `ℝⁿ⁺¹` is
`x ↦ (2 √(1 - ‖x‖²) x, 2 ‖x‖² - 1)`, the last coordinate being the height
(`TauCeti.closedBallToSphere`).  It sends the centre to the south pole `-e_last`, collapses the
boundary sphere to the north pole `e_last`, and is injective on the open ball.  The cube map
`TauCeti.cubeToSphere` precomposes it with the homeomorphism `TauCeti.diskHomeomorphCube` of the
disk onto the cube, the one through which `TauCeti.cubeBoundaryPair` and the Hurewicz maps are
compared with the disk.  In positive dimension it is surjective, hence a quotient map since the
cube is compact, and it induces the homeomorphism
`TauCeti.cubeQuotientHomeomorphSphere : Iⁿ / ∂Iⁿ ≃ₜ Sⁿ`, where `Iⁿ / ∂Iⁿ` is the quotient by the
relation `TauCeti.cubeBoundarySetoid` identifying all boundary points.

A generalized loop `p` therefore descends to a pointed map `GenLoop.toSphere p` out of the sphere,
and `GenLoop.sphereEquiv` identifies generalized loops with pointed maps.  Two generalized loops are
homotopic relative to the boundary of the cube exactly when the corresponding maps are homotopic
relative to the north pole (`GenLoop.homotopic_iff_toSphere`), so `πₙ(X, x)` is the set of
pointed homotopy classes of maps `(Sⁿ, e_last) → (X, x)` (`HomotopyGroup.sphereEquiv`).  The
identification is natural in based maps (`GenLoop.toSphere_map`).  A class is trivial exactly
when its map out of the sphere is null-homotopic, by a free homotopy that need not fix the north
pole (`HomotopyGroup.mk_eq_one_iff_nullhomotopic_toSphere`).

## Main declarations

* `TauCeti.sphereNorthPole`: the north pole `e_last` of the unit sphere of
  `EuclideanSpace ℝ (Fin (n + 1))`.
* `TauCeti.closedBallToSphere`: the closed unit ball of `ℝⁿ` modulo its boundary is the sphere,
  with `TauCeti.closedBallToSphere_eq_closedBallToSphere_iff` and
  `TauCeti.closedBallToSphere_surjective`.
* `TauCeti.cubeToSphere`: the same for the cube `I^n`, a quotient map in positive dimension
  (`TauCeti.isQuotientMap_cubeToSphere`) collapsing exactly the boundary
  (`TauCeti.cubeToSphere_eq_cubeToSphere_iff`, `TauCeti.cubeToSphere_eq_sphereNorthPole_iff`).
* `TauCeti.cubeQuotientHomeomorphSphere`: the pointed homeomorphism `Iⁿ / ∂Iⁿ ≃ₜ Sⁿ`.
* `TauCeti.sphereGenLoop`: `TauCeti.cubeToSphere` as a generalized loop of the sphere.
* `GenLoop.toSphere` and `GenLoop.sphereEquiv`: generalized loops are pointed maps out of the
  sphere; `p` is the image of `TauCeti.sphereGenLoop` under `GenLoop.toSphere p`
  (`GenLoop.map_toSphere_sphereGenLoop`).
* `GenLoop.diskBoundaryMap`: the map `GenLoop.toSphere p` with its source written as
  Mathlib's sphere `TopCat.diskBoundary (n + 1)`, the attaching map of a cell killing `⟦p⟧`.
* `GenLoop.diskMap`: a generalized loop `γ` of dimension `n` read on the disk `𝔻 n`, the map onto
  `γ` of a sphere formed by attaching an `n`-cell along a constant map.
* `GenLoop.homotopic_iff_toSphere` and `HomotopyGroup.sphereEquiv`: homotopy relative to the
  boundary of the cube is homotopy relative to the north pole, and `πₙ(X, x)` is the set of pointed
  homotopy classes of maps `Sⁿ → X`, the classes of `TauCeti.pointedHomotopySetoid`.
* `HomotopyGroup.mk_eq_one_iff_nullhomotopic_toSphere`: a class is trivial exactly when the
  corresponding map `Sⁿ → X` is freely null-homotopic.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, where `πₙ(X, x₀)` is described both by maps `(Iⁿ, ∂Iⁿ) → (X, x₀)` and, through
  `Iⁿ / ∂Iⁿ = Sⁿ`, by maps `(Sⁿ, s₀) → (X, x₀)`.
-/

public section

noncomputable section

universe u

open Metric Set Topology Topology.Homotopy
open scoped unitInterval

namespace TauCeti

section Ball

variable (n : ℕ)

/-- The north pole `e_last` of the unit sphere of `EuclideanSpace ℝ (Fin (n + 1))`: the last
standard basis vector. -/
def sphereNorthPole : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  ⟨EuclideanSpace.single (Fin.last n) 1, by simp⟩

@[simp]
lemma coe_sphereNorthPole :
    (sphereNorthPole n : EuclideanSpace ℝ (Fin (n + 1))) = EuclideanSpace.single (Fin.last n) 1 :=
  (rfl)

variable {n}

/-- A point of the unit sphere is the north pole exactly when its height is one. -/
theorem eq_sphereNorthPole_iff {y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1} :
    y = sphereNorthPole n ↔ (y : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n) = 1 := by
  refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
  have hy1 : ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by simp
  -- The horizontal coordinates have vanishing sum of squares.
  have hy2 : ∑ i : Fin n, (y : EuclideanSpace ℝ (Fin (n + 1))) i.castSucc ^ 2 = 0 := by
    have := EuclideanSpace.real_norm_sq_eq (y : EuclideanSpace ℝ (Fin (n + 1)))
    rw [Fin.sum_univ_castSucc, hy1, h] at this
    linarith
  have hzero (i : Fin n) : (y : EuclideanSpace ℝ (Fin (n + 1))) i.castSucc = 0 :=
    pow_eq_zero_iff two_ne_zero |>.1 <|
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ sq_nonneg _).1 hy2 i (Finset.mem_univ _)
  ext i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · simp [h]
  · simp [hzero, Fin.castSucc_ne_last]

/-- A point of the unit sphere has height less than one exactly when it is not the north pole. -/
theorem apply_last_lt_one_iff_ne_sphereNorthPole
    {y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1} :
    (y : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n) < 1 ↔ y ≠ sphereNorthPole n := by
  have hle : (y : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n) ≤ 1 := by
    have := PiLp.norm_apply_le (p := 2) (y : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n)
    rw [norm_eq_of_mem_sphere, Real.norm_eq_abs] at this
    exact (abs_le.1 this).2
  rw [hle.lt_iff_ne, Ne, Ne, eq_sphereNorthPole_iff]

/-- The vector underlying `TauCeti.closedBallToSphere`: `(2 √(1 - ‖x‖²) x, 2 ‖x‖² - 1)`. -/
private def closedBallToSphereAux (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ ↦ ℝ) (fun i ↦ 2 * √(1 - ‖x‖ ^ 2) * x i) (2 * ‖x‖ ^ 2 - 1))

private lemma closedBallToSphereAux_castSucc (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    closedBallToSphereAux x i.castSucc = 2 * √(1 - ‖x‖ ^ 2) * x i := by
  simp [closedBallToSphereAux]

private lemma closedBallToSphereAux_last (x : EuclideanSpace ℝ (Fin n)) :
    closedBallToSphereAux x (Fin.last n) = 2 * ‖x‖ ^ 2 - 1 := by
  simp [closedBallToSphereAux]

private lemma norm_closedBallToSphereAux {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ 1) :
    ‖closedBallToSphereAux x‖ = 1 := by
  have h₁ : 0 ≤ 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 ?_
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  simp only [closedBallToSphereAux_castSucc, closedBallToSphereAux_last, mul_pow,
    ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq, Real.sq_sqrt h₁]
  ring

variable (n) in
/-- **The closed unit ball modulo its boundary is the sphere.**  The map from the closed unit ball
of `ℝⁿ` to the unit sphere of `ℝⁿ⁺¹` sending `x` to `(2 √(1 - ‖x‖²) x, 2 ‖x‖² - 1)`, the last
coordinate being the height.  It sends the centre to the south pole, collapses the boundary sphere
to the north pole (`TauCeti.closedBallToSphere_eq_sphereNorthPole_iff`), is injective on the open
ball (`TauCeti.closedBallToSphere_eq_closedBallToSphere_iff`) and is surjective in positive
dimension (`TauCeti.closedBallToSphere_surjective`). -/
def closedBallToSphere :
    C(closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    where
  toFun x := ⟨closedBallToSphereAux x, by
    simpa using norm_closedBallToSphereAux (mem_closedBall_zero_iff.1 x.2)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ((PiLp.continuous_toLp 2 _).comp ?_) _
    refine Continuous.finSnoc (continuous_pi fun i ↦ ?_) ?_ <;> fun_prop

@[simp]
lemma closedBallToSphere_apply_castSucc (x : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (i : Fin n) :
    (closedBallToSphere n x : EuclideanSpace ℝ (Fin (n + 1))) i.castSucc =
      2 * √(1 - ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2) * (x : EuclideanSpace ℝ (Fin n)) i :=
  closedBallToSphereAux_castSucc _ i

@[simp]
lemma closedBallToSphere_apply_last (x : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (closedBallToSphere n x : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n) =
      2 * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 - 1 :=
  closedBallToSphereAux_last _

/-- `TauCeti.closedBallToSphere` sends exactly the boundary sphere to the north pole. -/
theorem closedBallToSphere_eq_sphereNorthPole_iff
    {x : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1} :
    closedBallToSphere n x = sphereNorthPole n ↔ ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  constructor
  · intro h
    have := congrArg (fun s : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
      (s : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n)) h
    simp only [closedBallToSphere_apply_last, coe_sphereNorthPole] at this
    simp only [PiLp.single_apply, ↓reduceIte] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (by linarith)
  · intro h
    ext i
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · norm_num [h]
    · simp [h, Fin.castSucc_ne_last]

private lemma norm_lt_one_of_closedBallToSphere_ne
    {x : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1}
    (hx : closedBallToSphere n x ≠ sphereNorthPole n) : ‖(x : EuclideanSpace ℝ (Fin n))‖ < 1 :=
  lt_of_le_of_ne (mem_closedBall_zero_iff.1 x.2) fun h ↦
    hx (closedBallToSphere_eq_sphereNorthPole_iff.2 h)

/-- `TauCeti.closedBallToSphere` identifies exactly the points of the boundary sphere: it is
injective on the open ball, and its value there is not the north pole. -/
theorem closedBallToSphere_eq_closedBallToSphere_iff
    {x y : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1} :
    closedBallToSphere n x = closedBallToSphere n y ↔
      x = y ∨ ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 ∧ ‖(y : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  constructor
  · intro h
    by_cases hx : closedBallToSphere n x = sphereNorthPole n
    · exact .inr ⟨closedBallToSphere_eq_sphereNorthPole_iff.1 hx,
        closedBallToSphere_eq_sphereNorthPole_iff.1 (h ▸ hx)⟩
    refine .inl ?_
    have hx' := norm_lt_one_of_closedBallToSphere_ne hx
    -- The heights agree, so the norms agree.
    have hnorm : ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 = ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
      have := congrArg (fun s : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
        (s : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n)) h
      simp only [closedBallToSphere_apply_last] at this
      linarith
    have hpos : 0 < 2 * √(1 - ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
      have : 0 < 1 - ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
        nlinarith [norm_nonneg (x : EuclideanSpace ℝ (Fin n))]
      positivity
    ext i
    have := congrArg (fun s : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
      (s : EuclideanSpace ℝ (Fin (n + 1))) i.castSucc) h
    simp only [closedBallToSphere_apply_castSucc, ← hnorm] at this
    exact mul_left_cancel₀ hpos.ne' this
  · rintro (rfl | ⟨hx, hy⟩)
    · rfl
    · rw [closedBallToSphere_eq_sphereNorthPole_iff.2 hx,
        closedBallToSphere_eq_sphereNorthPole_iff.2 hy]

/-- The point of the open ball sent by `TauCeti.closedBallToSphere` to a point `y` of the sphere
other than the north pole: the horizontal part of `y` divided by `2 √((1 - h) / 2)`, where `h` is
the height of `y`. -/
private def sphereToBallAux (y : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i ↦ y i.castSucc / (2 * √((1 - y (Fin.last n)) / 2))

private lemma norm_sq_sphereToBallAux {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : ‖y‖ = 1)
    (hlast : y (Fin.last n) < 1) :
    ‖sphereToBallAux y‖ ^ 2 = (1 + y (Fin.last n)) / 2 := by
  have hy2 : ∑ i : Fin n, y i.castSucc ^ 2 + y (Fin.last n) ^ 2 = 1 := by
    have := EuclideanSpace.real_norm_sq_eq y
    rw [Fin.sum_univ_castSucc, hy, one_pow] at this
    exact this.symm
  have h₁ : 0 < (1 - y (Fin.last n)) / 2 := by linarith
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [sphereToBallAux, PiLp.toLp_apply, div_pow, mul_pow, Real.sq_sqrt h₁.le,
    ← Finset.sum_div]
  rw [div_eq_div_iff (by positivity) two_ne_zero]
  nlinarith

/-- `TauCeti.closedBallToSphere` is surjective in positive dimension: the north pole is the image
of the boundary sphere, which is nonempty, and every other point of the sphere has an explicit
preimage in the open ball. -/
theorem closedBallToSphere_surjective [NeZero n] : Function.Surjective (closedBallToSphere n) := by
  intro y
  by_cases hy : y = sphereNorthPole n
  · subst hy
    refine ⟨⟨EuclideanSpace.single 0 1, by simp⟩, ?_⟩
    exact closedBallToSphere_eq_sphereNorthPole_iff.2 (by simp)
  have hy1 : ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by simp
  have hlast := apply_last_lt_one_iff_ne_sphereNorthPole.2 hy
  set x := sphereToBallAux (y : EuclideanSpace ℝ (Fin (n + 1)))
  have hx : ‖x‖ ^ 2 = (1 + (y : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n)) / 2 :=
    norm_sq_sphereToBallAux hy1 hlast
  have hxle : ‖x‖ ≤ 1 := by
    have : ‖x‖ ^ 2 ≤ 1 := by rw [hx]; linarith
    nlinarith [norm_nonneg x]
  refine ⟨⟨x, mem_closedBall_zero_iff.2 hxle⟩, ?_⟩
  have hsq : 1 - ‖x‖ ^ 2 = (1 - (y : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n)) / 2 := by
    rw [hx]; ring
  have hpos : 0 < 2 * √((1 - (y : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n)) / 2) := by
    have : 0 < (1 - (y : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n)) / 2 := by linarith
    positivity
  ext i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · rw [closedBallToSphere_apply_last]
    rw [Subtype.coe_mk, hx]
    ring
  · rw [closedBallToSphere_apply_castSucc]
    rw [Subtype.coe_mk, hsq]
    simp only [x, sphereToBallAux, PiLp.toLp_apply]
    exact mul_div_cancel₀ _ hpos.ne'

end Ball

section Cube

variable {n : ℕ}

variable (n) in
/-- **The cube modulo its boundary is the sphere.**  The map from the cube `I^n` to the unit sphere
of `EuclideanSpace ℝ (Fin (n + 1))` given by `TauCeti.closedBallToSphere` after the inverse of the
homeomorphism `TauCeti.diskHomeomorphCube` of the Euclidean disk onto the cube.  It collapses
exactly the boundary of the cube, to the north pole (`TauCeti.cubeToSphere_eq_sphereNorthPole_iff`,
`TauCeti.cubeToSphere_eq_cubeToSphere_iff`), and is a quotient map in positive dimension
(`TauCeti.isQuotientMap_cubeToSphere`). -/
def cubeToSphere : C(I^(Fin n), sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  (closedBallToSphere n).comp <|
    (Homeomorph.ulift.{0} (X := closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
      C(ULift.{0} (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1), _)).comp
      ((diskHomeomorphCube.{0} n).symm : C(I^(Fin n), TopCat.disk.{0} n))

lemma cubeToSphere_apply (y : I^(Fin n)) :
    cubeToSphere n y =
      closedBallToSphere n ((diskHomeomorphCube.{0} n).symm y :
        ULift.{0} (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down :=
  (rfl)

/-- `TauCeti.cubeToSphere` sends exactly the boundary of the cube to the north pole. -/
theorem cubeToSphere_eq_sphereNorthPole_iff {y : I^(Fin n)} :
    cubeToSphere n y = sphereNorthPole n ↔ y ∈ Cube.boundary (Fin n) := by
  rw [cubeToSphere_apply, closedBallToSphere_eq_sphereNorthPole_iff,
    norm_down_diskHomeomorphCube_symm_eq_one_iff]

/-- `TauCeti.cubeToSphere` identifies exactly the points of the boundary of the cube. -/
theorem cubeToSphere_eq_cubeToSphere_iff {y z : I^(Fin n)} :
    cubeToSphere n y = cubeToSphere n z ↔
      y = z ∨ y ∈ Cube.boundary (Fin n) ∧ z ∈ Cube.boundary (Fin n) := by
  rw [cubeToSphere_apply, cubeToSphere_apply, closedBallToSphere_eq_closedBallToSphere_iff,
    norm_down_diskHomeomorphCube_symm_eq_one_iff, norm_down_diskHomeomorphCube_symm_eq_one_iff]
  exact or_congr_left
    ⟨fun h ↦ (diskHomeomorphCube.{0} n).symm.injective (ULift.ext h), fun h ↦ h ▸ rfl⟩

variable (n) in
/-- **The tautological generalized loop of the sphere**: `TauCeti.cubeToSphere`, which sends the
boundary of the cube to the north pole, as a generalized loop at the north pole. Every generalized
loop `p` is its image under the pointed map `GenLoop.toSphere p`
(`GenLoop.map_toSphere_sphereGenLoop`). -/
def sphereGenLoop :
    Ω^ (Fin n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (sphereNorthPole n) :=
  ⟨cubeToSphere n, fun _ hy ↦ cubeToSphere_eq_sphereNorthPole_iff.2 hy⟩

@[simp]
lemma sphereGenLoop_apply (y : I^(Fin n)) : sphereGenLoop n y = cubeToSphere n y :=
  (rfl)

variable (n) in
/-- `TauCeti.cubeToSphere` is surjective in positive dimension. -/
theorem cubeToSphere_surjective [NeZero n] : Function.Surjective (cubeToSphere n) :=
  (closedBallToSphere_surjective).comp <|
    Homeomorph.ulift.surjective.comp (diskHomeomorphCube.{0} n).symm.surjective

variable (n) in
/-- `TauCeti.cubeToSphere` is a quotient map in positive dimension: it is a continuous surjection
from the compact cube onto the Hausdorff sphere. -/
theorem isQuotientMap_cubeToSphere [NeZero n] : IsQuotientMap (cubeToSphere n) :=
  (cubeToSphere n).continuous.isClosedMap.isQuotientMap (cubeToSphere n).continuous
    (cubeToSphere_surjective n)

variable (n) in
/-- **The cube modulo its boundary is homeomorphic to the sphere**, by the map induced by
`TauCeti.cubeToSphere`.  It is pointed: the class of the boundary goes to the north pole. -/
def cubeQuotientHomeomorphSphere [NeZero n] :
    Quotient (cubeBoundarySetoid (Fin n)) ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  (Homeomorph.Quotient.congrRight fun _ _ ↦
    cubeBoundarySetoid_iff.trans cubeToSphere_eq_cubeToSphere_iff.symm).trans
    (isQuotientMap_cubeToSphere n).homeomorph

@[simp]
lemma cubeQuotientHomeomorphSphere_mk [NeZero n] (y : I^(Fin n)) :
    cubeQuotientHomeomorphSphere n ⟦y⟧ = cubeToSphere n y := by
  unfold cubeQuotientHomeomorphSphere
  rfl

/-- `TauCeti.cubeQuotientHomeomorphSphere` is pointed: it sends the class of the boundary of the
cube to the north pole. -/
lemma cubeQuotientHomeomorphSphere_mk_of_mem_boundary [NeZero n] {y : I^(Fin n)}
    (hy : y ∈ Cube.boundary (Fin n)) :
    cubeQuotientHomeomorphSphere n ⟦y⟧ = sphereNorthPole n :=
  (cubeQuotientHomeomorphSphere_mk y).trans (cubeToSphere_eq_sphereNorthPole_iff.2 hy)

/-- The inverse of `TauCeti.cubeQuotientHomeomorphSphere` sends the north pole to the class of the
boundary of the cube, represented by its corner `0`. -/
@[simp]
lemma cubeQuotientHomeomorphSphere_symm_sphereNorthPole [NeZero n] :
    (cubeQuotientHomeomorphSphere n).symm (sphereNorthPole n) = ⟦0⟧ :=
  (Homeomorph.symm_apply_eq _).2
    (cubeQuotientHomeomorphSphere_mk_of_mem_boundary zero_mem_cubeBoundary).symm

end Cube

end TauCeti

namespace GenLoop

open TauCeti

variable {n : ℕ} [NeZero n] {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X}
  {y : Y}

omit [NeZero n] in
/-- A generalized loop is constant on the fibres of `TauCeti.cubeToSphere`. -/
private lemma factorsThrough_cubeToSphere (p : Ω^ (Fin n) X x) :
    Function.FactorsThrough p.1 (cubeToSphere n) := fun y z h ↦ by
  rcases cubeToSphere_eq_cubeToSphere_iff.1 h with rfl | ⟨hy, hz⟩
  · rfl
  · exact (p.2 y hy).trans (p.2 z hz).symm

/-- A generalized loop `I^n → X`, constant on the boundary of the cube, descends along
`TauCeti.cubeToSphere` to a map out of the unit sphere of `EuclideanSpace ℝ (Fin (n + 1))`
(`GenLoop.toSphere_cubeToSphere`), sending the north pole to the base point
(`GenLoop.toSphere_sphereNorthPole`). -/
def toSphere (p : Ω^ (Fin n) X x) : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, X) :=
  (isQuotientMap_cubeToSphere n).lift p.1 (factorsThrough_cubeToSphere p)

@[simp]
theorem toSphere_cubeToSphere (p : Ω^ (Fin n) X x) (z : I^(Fin n)) :
    toSphere p (cubeToSphere n z) = p z :=
  DFunLike.congr_fun ((isQuotientMap_cubeToSphere n).lift_comp _ (factorsThrough_cubeToSphere p)) z

@[simp]
theorem toSphere_sphereNorthPole (p : Ω^ (Fin n) X x) : toSphere p (sphereNorthPole n) = x := by
  rw [← cubeToSphere_eq_sphereNorthPole_iff.2 zero_mem_cubeBoundary, toSphere_cubeToSphere]
  exact p.2 0 zero_mem_cubeBoundary

/-- The pointed map out of the sphere of the image of a generalized loop under a based map is the
composite. -/
@[simp]
theorem toSphere_map (f : C(X, Y)) (hf : f x = y) (p : Ω^ (Fin n) X x) :
    toSphere (GenLoop.map f hf p) = f.comp (toSphere p) := by
  ext s
  obtain ⟨z, rfl⟩ := cubeToSphere_surjective n s
  simp

/-- **Every generalized loop is an image of the tautological loop**: `p` is the image of
`TauCeti.sphereGenLoop n` under the pointed map `GenLoop.toSphere p` out of the sphere. -/
@[simp]
theorem map_toSphere_sphereGenLoop (p : Ω^ (Fin n) X x) :
    GenLoop.map (toSphere p) (toSphere_sphereNorthPole p) (sphereGenLoop n) = p := by
  ext z
  simp

/-- The constant generalized loop corresponds to the constant map out of the sphere. -/
@[simp]
theorem toSphere_const : toSphere (const : Ω^ (Fin n) X x) = ContinuousMap.const _ x := by
  ext s
  obtain ⟨z, rfl⟩ := cubeToSphere_surjective n s
  simp [const_apply]

variable (n X x) in
/-- **Generalized loops are pointed maps out of the sphere.**  The bijection between generalized
loops `(I^n, ∂I^n) → (X, x)` and pointed maps `(Sⁿ, e_last) → (X, x)` out of the unit sphere of
`EuclideanSpace ℝ (Fin (n + 1))`, given by `GenLoop.toSphere` and by precomposition with
`TauCeti.cubeToSphere`. -/
def sphereEquiv :
    Ω^ (Fin n) X x ≃
      {f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, X) // f (sphereNorthPole n) = x} where
  toFun p := ⟨toSphere p, toSphere_sphereNorthPole p⟩
  invFun f := ⟨f.1.comp (cubeToSphere n), fun z hz ↦ by
    simp [cubeToSphere_eq_sphereNorthPole_iff.2 hz, f.2]⟩
  left_inv p := by
    ext z
    exact toSphere_cubeToSphere p z
  right_inv f := by
    ext s
    obtain ⟨z, rfl⟩ := cubeToSphere_surjective n s
    exact toSphere_cubeToSphere _ z

@[simp]
lemma coe_sphereEquiv_apply (p : Ω^ (Fin n) X x) : (sphereEquiv n X x p).1 = toSphere p :=
  (rfl)

@[simp]
lemma coe_sphereEquiv_symm_apply
    (f : {f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, X) // f (sphereNorthPole n) = x}) :
    ((sphereEquiv n X x).symm f).1 = f.1.comp (cubeToSphere n) :=
  (rfl)

@[simp]
lemma sphereEquiv_symm_apply_apply
    (f : {f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, X) // f (sphereNorthPole n) = x})
    (z : I^(Fin n)) :
    (sphereEquiv n X x).symm f z = f.1 (cubeToSphere n z) :=
  (rfl)

/-- **Homotopies of generalized loops are pointed homotopies of maps out of the sphere.**  Two
generalized loops are homotopic relative to the boundary of the cube exactly when the corresponding
maps out of the sphere are homotopic relative to the north pole. -/
theorem homotopic_iff_toSphere {p q : Ω^ (Fin n) X x} :
    GenLoop.Homotopic p q ↔ (toSphere p).HomotopicRel (toSphere q) {sphereNorthPole n} := by
  -- The product of `cubeToSphere` with the identity of `I` is again a quotient map, as a
  -- continuous surjection from a compact space onto a Hausdorff space.
  let c : C(I × I^(Fin n), I × sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    (ContinuousMap.id I).prodMap (cubeToSphere n)
  have hc : IsQuotientMap c :=
    c.continuous.isClosedMap.isQuotientMap c.continuous
      (Function.surjective_id.prodMap (cubeToSphere_surjective n))
  constructor
  · rintro ⟨H⟩
    have hH : Function.FactorsThrough H.toContinuousMap c := by
      rintro ⟨s, y⟩ ⟨t, z⟩ h
      simp only [c, ContinuousMap.prodMap_apply, ContinuousMap.id_apply, Prod.map_apply,
        Prod.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      rcases cubeToSphere_eq_cubeToSphere_iff.1 h with rfl | ⟨hy, hz⟩
      · rfl
      · exact (H.eq_fst s hy).trans <|
          (p.2 y hy).trans <| (p.2 z hz).symm.trans (H.eq_fst s hz).symm
    have hlift (t : I) (z : I^(Fin n)) : hc.lift H.toContinuousMap hH (t, cubeToSphere n z) =
        H (t, z) :=
      DFunLike.congr_fun (hc.lift_comp H.toContinuousMap hH) (t, z)
    refine ⟨⟨⟨hc.lift H.toContinuousMap hH, fun s ↦ ?_, fun s ↦ ?_⟩, fun t s hs ↦ ?_⟩⟩
    · obtain ⟨z, rfl⟩ := cubeToSphere_surjective n s
      simpa using hlift 0 z
    · obtain ⟨z, rfl⟩ := cubeToSphere_surjective n s
      simpa using hlift 1 z
    · obtain rfl := Set.mem_singleton_iff.1 hs
      rw [← cubeToSphere_eq_sphereNorthPole_iff.2 zero_mem_cubeBoundary]
      simpa using (hlift t 0).trans (H.eq_fst t zero_mem_cubeBoundary)
  · rintro ⟨G⟩
    refine ⟨⟨⟨G.toContinuousMap.comp c, fun z ↦ ?_, fun z ↦ ?_⟩, fun t z hz ↦ ?_⟩⟩
    · simp [c]
    · simp [c]
    · simpa [c] using G.eq_fst t
        (Set.mem_singleton_iff.2 (cubeToSphere_eq_sphereNorthPole_iff.2 hz))

end GenLoop

namespace GenLoop

variable {n : ℕ} [NeZero n] {X : TopCat.{u}} {x : X}

/-- The attaching map `∂𝔻 (n + 1) ⟶ X` of the `(n + 1)`-cell that kills the class of a generalized
loop `p`: the pointed map `Sⁿ → X` corresponding to `p` (`GenLoop.toSphere`), with its source
written as Mathlib's sphere `TopCat.diskBoundary (n + 1)`. -/
def diskBoundaryMap (p : Ω^ (Fin n) X x) : TopCat.diskBoundary.{u} (n + 1) ⟶ X :=
  TopCat.ofHom ((GenLoop.toSphere p).comp ⟨ULift.down, continuous_uliftDown⟩)

@[simp]
theorem diskBoundaryMap_apply (p : Ω^ (Fin n) X x) (s : TopCat.diskBoundary.{u} (n + 1)) :
    diskBoundaryMap p s = GenLoop.toSphere p s.down :=
  (rfl)

open CategoryTheory in
/-- The attaching map of the image of a generalized loop under a based map is the attaching map of
the loop followed by the map. -/
@[simp]
theorem diskBoundaryMap_map {Y : TopCat.{u}} (f : X ⟶ Y) {y : Y} (hf : f x = y)
    (p : Ω^ (Fin n) X x) : diskBoundaryMap (GenLoop.map f.hom hf p) = diskBoundaryMap p ≫ f := by
  ext s
  simp

end GenLoop

namespace GenLoop

open TauCeti

variable {n : ℕ} {X : TopCat.{u}} {x : X}

/-- A generalized loop `γ` of dimension `n`, read on the disk `𝔻 n` through
`TauCeti.diskHomeomorphCube`. When `TopCat.diskBoundary n` is attached at `x` along a constant
map, this is the map onto `γ` of the resulting sphere. -/
def diskMap (γ : Ω^ (Fin n) X x) : TopCat.disk.{u} n ⟶ X :=
  TopCat.ofHom (γ.1.comp (diskHomeomorphCube n : C(TopCat.disk.{u} n, I^(Fin n))))

@[simp]
theorem diskMap_apply (γ : Ω^ (Fin n) X x) (s : TopCat.disk.{u} n) :
    diskMap γ s = γ (diskHomeomorphCube n s) :=
  (rfl)

open CategoryTheory in
/-- A generalized loop at `x`, read on the disk, is constant at `x` on the boundary sphere. -/
@[reassoc (attr := simp)]
theorem diskBoundaryInclusion_comp_diskMap (γ : Ω^ (Fin n) X x) :
    TopCat.diskBoundaryInclusion n ≫ diskMap γ = TopCat.ofHom (ContinuousMap.const _ x) := by
  ext s
  -- The boundary sphere of the disk goes to the boundary of the cube, where `γ` is `x`.
  exact γ.2 _ ((diskHomeomorphCube_mem_boundary_iff _).2 ⟨s, rfl⟩)

end GenLoop

namespace HomotopyGroup

open TauCeti

variable {n : ℕ} [NeZero n] {X : Type*} [TopologicalSpace X] {x : X}

variable (n X x) in
/-- **Homotopy groups are pointed homotopy classes of maps out of spheres.**  The bijection
between `πₙ(X, x)` and the pointed homotopy classes of maps `(Sⁿ, e_last) → (X, x)` out of the unit
sphere of `EuclideanSpace ℝ (Fin (n + 1))`, induced by `GenLoop.sphereEquiv`. -/
def sphereEquiv :
    HomotopyGroup (Fin n) X x ≃ Quotient (pointedHomotopySetoid (sphereNorthPole n) x) :=
  Quotient.congr (GenLoop.sphereEquiv n X x) fun _ _ ↦ by
    rw [pointedHomotopySetoid_iff, GenLoop.coe_sphereEquiv_apply, GenLoop.coe_sphereEquiv_apply]
    exact GenLoop.homotopic_iff_toSphere

@[simp]
lemma sphereEquiv_mk (p : Ω^ (Fin n) X x) :
    sphereEquiv n X x ⟦p⟧ = ⟦GenLoop.sphereEquiv n X x p⟧ := by
  unfold sphereEquiv
  exact Quotient.congr_mk _ _ p

/-- **A homotopy class is trivial exactly when its sphere map is null-homotopic.** The class of a
generalized loop `p` is the identity of `πₙ(X, x)` if and only if the corresponding map
`GenLoop.toSphere p : Sⁿ → X` is freely homotopic to a constant map. -/
theorem mk_eq_one_iff_nullhomotopic_toSphere (p : Ω^ (Fin n) X x) :
    (⟦p⟧ : HomotopyGroup (Fin n) X x) = (1 : HomotopyGroup (Fin n) X x) ↔
      (GenLoop.toSphere p).Nullhomotopic := by
  constructor
  · intro h
    have h' := (GenLoop.homotopic_iff_toSphere.1 (Quotient.exact (h.trans one_def))).homotopic
    rw [GenLoop.toSphere_const] at h'
    exact ⟨x, h'⟩
  · intro h
    -- `p` is the image under `GenLoop.toSphere p` of the tautological generalized loop of the
    -- sphere, the one corresponding to its identity map.
    have hp : GenLoop.map (GenLoop.toSphere p) (GenLoop.toSphere_sphereNorthPole p)
        ((GenLoop.sphereEquiv n _ _).symm ⟨ContinuousMap.id _, ContinuousMap.id_apply _⟩) = p :=
      GenLoop.ext _ _ fun z ↦ by simp
    rw [← hp, ← map_mk]
    exact map_eq_one_of_nullhomotopic h _ _

/-- **A homotopy class is trivial exactly when its attaching map is null-homotopic.** The class of
a generalized loop `p` is the identity of `πₙ(X, x)` if and only if the map
`GenLoop.diskBoundaryMap p : ∂𝔻 (n + 1) ⟶ X`, along which a cell kills that class, is freely
null-homotopic. -/
theorem mk_eq_one_iff_nullhomotopic_diskBoundaryMap {X : TopCat.{u}} {x : X}
    (p : Ω^ (Fin n) X x) :
    (⟦p⟧ : HomotopyGroup (Fin n) X x) = (1 : HomotopyGroup (Fin n) X x) ↔
      (GenLoop.diskBoundaryMap p).hom.Nullhomotopic := by
  rw [mk_eq_one_iff_nullhomotopic_toSphere]
  -- The attaching map is `GenLoop.toSphere p` precomposed with `ULift.down`, and conversely
  -- `GenLoop.toSphere p` is the attaching map precomposed with `ULift.up`.
  refine ⟨fun h ↦ h.comp_left ⟨ULift.down, continuous_uliftDown⟩, fun h ↦ ?_⟩
  have hp : GenLoop.toSphere p =
      (GenLoop.diskBoundaryMap p).hom.comp ⟨ULift.up, continuous_uliftUp⟩ := by
    ext s
    exact (GenLoop.diskBoundaryMap_apply p ⟨s⟩).symm
  exact hp ▸ h.comp_left _

open CategoryTheory in
/-- **A based map kills a class exactly when it extends the attaching map over a disk.** The image
of the class of `p` under a based map `f` is the identity exactly when the attaching map
`GenLoop.diskBoundaryMap p` followed by `f` is null-homotopic. -/
theorem map_mk_eq_one_iff_nullhomotopic_diskBoundaryMap_comp {X Y : TopCat.{u}} {x : X} {y : Y}
    (f : X ⟶ Y) (hf : f x = y) (p : Ω^ (Fin n) X x) :
    map f.hom hf (⟦p⟧ : HomotopyGroup (Fin n) X x) = 1 ↔
      (GenLoop.diskBoundaryMap p ≫ f).hom.Nullhomotopic := by
  rw [map_mk, ← GenLoop.diskBoundaryMap_map f hf]
  exact mk_eq_one_iff_nullhomotopic_diskBoundaryMap _

end HomotopyGroup
