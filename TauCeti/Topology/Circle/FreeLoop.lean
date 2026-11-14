/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Instances.Int
public import TauCeti.Topology.Circle.Degree
public import TauCeti.Topology.Circle.Loop
public import TauCeti.Topology.Constructions.SumProd
public import TauCeti.Topology.MappingSpace.FreeLoop

/-!
# The free loop space of the circle

The free loop space `𝓛S¹ = C(S¹, S¹)` of the circle is homotopy equivalent to `ℤ × S¹`
(`Circle.freeLoopHomotopyEquiv`). The equivalence sends a loop `f` to its degree and to its value
`f 1`; its homotopy inverse sends `(n, z)` to the loop `w ↦ z * w ^ n`. So the path components of
`𝓛S¹` are indexed by the degree, and each of them is homotopy equivalent to the circle through
evaluation at `1`.

The degree of `f` is read off from a lift of the normalized loop `t ↦ (f 1)⁻¹ * f (e^{2πit})`
through `Circle.exp`. Mathlib's homotopy lifting for the covering `Circle.exp` lifts these loops
continuously in `f`, starting at the angle `0`. The lift `Θ f` ends at `2π` times the degree, which
is therefore locally constant in `f`. Interpolating linearly between `Θ f` and the angle function
`t ↦ 2π n t` of `w ↦ w ^ n` gives a homotopy from `f` to `w ↦ f 1 * w ^ n` through closed loops,
continuous in `f`.

## Main declarations

* `Circle.freeLoopHomotopyEquiv`: the homotopy equivalence `C(S¹, S¹) ≃ₕ ℤ × S¹`.
* `Circle.freeLoopHomotopyEquiv_symm_apply`: its homotopy inverse is `(n, z) ↦ (w ↦ z * w ^ n)`.
* `Circle.freeLoopHomotopyEquiv_apply_symm_apply`: the equivalence is a left inverse of its
  homotopy inverse.
* `ContinuousMap.circleDegree`: the degree of a circle map, continuous in the map
  (`ContinuousMap.continuous_circleDegree`).
* `ContinuousMap.sub_eq_circleDegree_mul`, `ContinuousMap.circleDegree_eq_degree`: the degree is
  read off from any continuous angle function or from any loop `γ` with `γ t = f (e^{2πit})`.
* `ContinuousMap.circleDegree_toCircle`, `ContinuousMap.circleDegree_freeLoopHomotopyEquiv_symm`:
  a loop read as a circle map has its degree, and `w ↦ z * w ^ n` has degree `n`.
* `Circle.freeLoopHomotopyEquiv_apply`: the equivalence is `f ↦ (f.circleDegree, f 1)`.
* `Circle.freeLoopHomotopyEquiv_toCircle`: a loop `γ` at `x`, read as a circle map, goes to
  `(degree γ, x)`.
* `Circle.sigmaFreeLoopHomotopyEquiv`, `Circle.freeLoopComponentInclusion`: the same equivalence
  from the disjoint union `Σ m : ℤ, S¹`, and its restriction `z ↦ (w ↦ z * w ^ m)` to the copy of
  index `m`, into the loops of degree `m`.
* `Circle.freeLoopHomotopyEquiv_freeLoopComponentInclusion`: the loop `w ↦ z * w ^ m` goes to
  `(m, z)`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 1.30 and §1.1.
-/

public section

noncomputable section

open Real TauCeti
open scoped unitInterval

namespace Circle

/-- The normalized loops `t ↦ (f 1)⁻¹ * f (e^{2πit})` of the circle maps `f`, as a family over
`C(S¹, S¹)` of paths starting at `1`. -/
private def normalizedLoopFamily : C(I × C(Circle, Circle), Circle) :=
  ⟨fun p ↦ (p.2 1)⁻¹ * p.2 (unitToCircle p.1), by fun_prop⟩

/-- The angle function of the normalized loop of `f`, lifted through `Circle.exp` continuously in
`f` and starting at `0`. -/
private noncomputable def freeLoopAngle : C(I × C(Circle, Circle), ℝ) :=
  isCoveringMap_exp.liftHomotopy normalizedLoopFamily (ContinuousMap.const _ 0)
    fun f ↦ by simp [normalizedLoopFamily, unitToCircle_zero]

private theorem exp_freeLoopAngle (t : I) (f : C(Circle, Circle)) :
    exp (freeLoopAngle (t, f)) = (f 1)⁻¹ * f (unitToCircle t) :=
  congr_fun (isCoveringMap_exp.liftHomotopy_lifts normalizedLoopFamily _ _) (t, f)

private theorem freeLoopAngle_zero (f : C(Circle, Circle)) : freeLoopAngle (0, f) = 0 :=
  isCoveringMap_exp.liftHomotopy_zero normalizedLoopFamily _ _ f

/-- The normalized loop `t ↦ (f 1)⁻¹ * f (e^{2πit})` of a circle map, based at `1`. -/
private def normalizedLoop (f : C(Circle, Circle)) : Path (1 : Circle) 1 where
  toFun t := (f 1)⁻¹ * f (unitToCircle t)
  source' := by simp [unitToCircle_zero]
  target' := by simp [unitToCircle_one]

/-- The **degree** of a circle map `f`: the degree of the loop `t ↦ f (e^{2πit})`, the number of
times `f` winds counterclockwise around the circle. It is computed from any continuous angle
function of that loop (`ContinuousMap.sub_eq_circleDegree_mul`). -/
noncomputable def _root_.ContinuousMap.circleDegree (f : C(Circle, Circle)) : ℤ :=
  degree (normalizedLoop f)

/-- The lifted angle of the normalized loop of `f` ends at `2π` times the degree of `f`. -/
private theorem freeLoopAngle_one (f : C(Circle, Circle)) :
    freeLoopAngle (1, f) = f.circleDegree * (2 * π) := by
  have h := sub_eq_degree_mul (normalizedLoop f) (θ := fun t ↦ freeLoopAngle (t, f))
    (by fun_prop) fun t ↦ exp_freeLoopAngle t f
  rwa [freeLoopAngle_zero, sub_zero] at h

/-- The degree of a circle map `f` is read off from any continuous angle function `θ` of its loop,
`exp (θ t) = f (e^{2πit})`: `θ` changes by that many full turns. -/
theorem _root_.ContinuousMap.sub_eq_circleDegree_mul (f : C(Circle, Circle)) {θ : I → ℝ}
    (hθ : Continuous θ) (hθf : ∀ t, exp (θ t) = f (unitToCircle t)) :
    θ 1 - θ 0 = f.circleDegree * (2 * π) := by
  -- `θ - θ 0` is another continuous lift of the normalized loop, since `exp (θ 0) = f 1`.
  have h := sub_eq_degree_mul (normalizedLoop f) (θ := fun t ↦ θ t - θ 0) (by fun_prop)
    fun t ↦ by simp [normalizedLoop, exp_sub, hθf, div_eq_inv_mul]
  simpa [ContinuousMap.circleDegree] using h

/-- The degree of a circle map is continuous, that is, locally constant, in the map. -/
theorem _root_.ContinuousMap.continuous_circleDegree :
    Continuous ContinuousMap.circleDegree := by
  rw [Int.isClosedEmbedding_coe_real.continuous_iff]
  have h : ((↑) : ℤ → ℝ) ∘ ContinuousMap.circleDegree = fun f ↦ freeLoopAngle (1, f) / (2 * π) := by
    ext f
    simp [freeLoopAngle_one, Real.pi_ne_zero]
  rw [h]
  fun_prop

/-- The circle map `w ↦ z * w ^ n`. -/
private def powLoop (p : ℤ × Circle) : C(Circle, Circle) :=
  ⟨fun w ↦ p.2 * w ^ p.1, by fun_prop⟩

private theorem powLoop_apply (p : ℤ × Circle) (w : Circle) : powLoop p w = p.2 * w ^ p.1 :=
  (rfl)

private theorem continuous_powLoop : Continuous powLoop := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have h : Function.uncurry (fun p ↦ powLoop p) =
      fun q : (ℤ × Circle) × Circle ↦ q.1.2 * q.2 ^ q.1.1 :=
    funext fun q ↦ powLoop_apply q.1 q.2
  rw [h]
  -- the integer coordinate is discrete, so continuity can be checked one integer at a time
  have hpow : Continuous fun q : ℤ × Circle ↦ q.2 ^ q.1 :=
    continuous_prod_of_discrete_left.2 fun n ↦ continuous_zpow n
  exact (continuous_snd.comp continuous_fst).mul
    (hpow.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))

private theorem circleDegree_powLoop (p : ℤ × Circle) : (powLoop p).circleDegree = p.1 := by
  refine degree_eq_of_sub_eq (normalizedLoop (powLoop p)) (θ := fun t ↦ p.1 * (2 * π * t))
    (by fun_prop) (fun t ↦ ?_) (by simp)
  simp [normalizedLoop, powLoop_apply, unitToCircle_apply, exp_intCast_mul]

/-- The straight-line homotopy of angle functions from `t ↦ 2π n t` to the lifted angle of `f`,
as a family of closed unit-interval loops at `f 1`. -/
private noncomputable def straighteningAngle (q : (I × C(Circle, Circle)) × I) : ℝ :=
  q.1.1 * freeLoopAngle (q.2, q.1.2) + (1 - q.1.1) * (q.1.2.circleDegree * (2 * π * q.2))

private theorem continuous_straighteningAngle : Continuous straighteningAngle := by
  have hdeg : Continuous fun q : (I × C(Circle, Circle)) × I ↦ (q.1.2.circleDegree : ℝ) :=
    (continuous_of_discreteTopology (f := ((↑) : ℤ → ℝ))).comp
      (ContinuousMap.continuous_circleDegree.comp (continuous_snd.comp continuous_fst))
  unfold straighteningAngle
  fun_prop

private theorem straighteningAngle_zero (p : I × C(Circle, Circle)) :
    straighteningAngle (p, 0) = 0 := by
  simp [straighteningAngle, freeLoopAngle_zero]

private theorem straighteningAngle_one (p : I × C(Circle, Circle)) :
    straighteningAngle (p, 1) = p.2.circleDegree * (2 * π) := by
  simp only [straighteningAngle, freeLoopAngle_one, Set.Icc.coe_one, mul_one]
  ring

/-- The loops `t ↦ f 1 * exp (straighteningAngle ((s, f), t))`, closed since the angle changes by
`2π` times the degree of `f`. -/
private def straighteningLoop : C(I × C(Circle, Circle), ClosedUnitPath Circle) :=
  ⟨fun p ↦ ⟨(ContinuousMap.curry ⟨fun q : (I × C(Circle, Circle)) × I ↦
      q.1.2 1 * exp (straighteningAngle q), by
        have := continuous_straighteningAngle
        fun_prop⟩) p, by
      simp only [ContinuousMap.curry_apply, ContinuousMap.coe_mk]
      rw [straighteningAngle_zero, straighteningAngle_one, exp_zero, exp_int_mul_two_pi]⟩,
    (ContinuousMap.continuous _).subtype_mk _⟩

private theorem straighteningLoop_apply (p : I × C(Circle, Circle)) (t : I) :
    (straighteningLoop p).1 t = p.2 1 * exp (straighteningAngle (p, t)) :=
  rfl

/-- The straightening homotopy, read as a family of circle maps. -/
private def straighteningHomotopy : C(I × C(Circle, Circle), C(Circle, Circle)) :=
  ⟨fun p ↦ circleMapHomeomorphClosedUnitPath.symm (straighteningLoop p),
    circleMapHomeomorphClosedUnitPath.symm.continuous.comp straighteningLoop.continuous⟩

private theorem straighteningHomotopy_unitToCircle (p : I × C(Circle, Circle)) (t : I) :
    straighteningHomotopy p (unitToCircle t) = p.2 1 * exp (straighteningAngle (p, t)) := by
  simp [straighteningHomotopy, circleMapHomeomorphClosedUnitPath_symm_unitToCircle,
    straighteningLoop_apply]

/-- A circle map goes to its degree and its value at `1`. -/
private def degreeEval : C(C(Circle, Circle), ℤ × Circle) :=
  ⟨fun f ↦ (f.circleDegree, f 1),
    ContinuousMap.continuous_circleDegree.prodMk (continuous_eval_const 1)⟩

private theorem degreeEval_apply (f : C(Circle, Circle)) :
    degreeEval f = (f.circleDegree, f 1) :=
  (rfl)

private theorem degreeEval_powLoop (p : ℤ × Circle) : degreeEval (powLoop p) = p := by
  simp [degreeEval_apply, circleDegree_powLoop, powLoop_apply]

private theorem degreeEval_comp_powLoop :
    degreeEval.comp ⟨powLoop, continuous_powLoop⟩ = ContinuousMap.id _ :=
  ContinuousMap.ext degreeEval_powLoop

/-- The **free loop space of the circle** is homotopy equivalent to `ℤ × S¹`. A loop `f` goes to
its degree and its value `f 1`; the homotopy inverse sends `(n, z)` to the loop `w ↦ z * w ^ n`. -/
def freeLoopHomotopyEquiv : ContinuousMap.HomotopyEquiv C(Circle, Circle) (ℤ × Circle) where
  toFun := degreeEval
  invFun := ⟨powLoop, continuous_powLoop⟩
  left_inv := ⟨{
    toContinuousMap := straighteningHomotopy
    map_zero_left f := ContinuousMap.ext_unitToCircle fun t ↦ by
      rw [ContinuousMap.toFun_eq_coe, straighteningHomotopy_unitToCircle]
      simp [straighteningAngle, degreeEval_apply, powLoop_apply, unitToCircle_apply,
        ← exp_intCast_mul, mul_assoc]
    map_one_left f := ContinuousMap.ext_unitToCircle fun t ↦ by
      rw [ContinuousMap.toFun_eq_coe, straighteningHomotopy_unitToCircle]
      simp [straighteningAngle, exp_freeLoopAngle] }⟩
  right_inv := by rw [degreeEval_comp_powLoop]

/-- The homotopy inverse of `Circle.freeLoopHomotopyEquiv` sends `(n, z)` to `w ↦ z * w ^ n`. -/
@[simp]
theorem freeLoopHomotopyEquiv_symm_apply (p : ℤ × Circle) (w : Circle) :
    freeLoopHomotopyEquiv.symm p w = p.2 * w ^ p.1 :=
  (rfl)

/-- `Circle.freeLoopHomotopyEquiv` recovers `(n, z)` from the loop `w ↦ z * w ^ n`: that loop has
degree `n` and value `z` at `1`. -/
@[simp]
theorem freeLoopHomotopyEquiv_apply_symm_apply (p : ℤ × Circle) :
    freeLoopHomotopyEquiv (freeLoopHomotopyEquiv.symm p) = p :=
  degreeEval_powLoop p

/-- `Circle.freeLoopHomotopyEquiv` sends a circle map to its degree and its value at `1`. -/
theorem freeLoopHomotopyEquiv_apply (f : C(Circle, Circle)) :
    freeLoopHomotopyEquiv f = (f.circleDegree, f 1) :=
  (rfl)

/-- The integer coordinate of `Circle.freeLoopHomotopyEquiv` is the degree. -/
@[simp]
theorem freeLoopHomotopyEquiv_apply_fst (f : C(Circle, Circle)) :
    (freeLoopHomotopyEquiv f).1 = f.circleDegree :=
  (rfl)

/-- The circle coordinate of `Circle.freeLoopHomotopyEquiv` is evaluation at `1`. -/
@[simp]
theorem freeLoopHomotopyEquiv_apply_snd (f : C(Circle, Circle)) :
    (freeLoopHomotopyEquiv f).2 = f 1 :=
  (rfl)

/-- The degree of a circle map `f` is the degree of any loop `γ` tracing `f`,
`γ t = f (e^{2πit})`. -/
theorem _root_.ContinuousMap.circleDegree_eq_degree (f : C(Circle, Circle)) {x : Circle}
    (γ : Path x x) (hγ : ∀ t, γ t = f (unitToCircle t)) : f.circleDegree = degree γ := by
  obtain ⟨θ, hθ⟩ := exists_lift γ
  have h := f.sub_eq_circleDegree_mul θ.continuous fun t ↦ (hθ t).trans (hγ t)
  exact (degree_eq_of_sub_eq γ θ.continuous hθ h).symm

/-- A loop `γ`, read as a circle map, has the degree of `γ`. -/
@[simp]
theorem _root_.ContinuousMap.circleDegree_toCircle {x : Circle} (γ : Path x x) :
    γ.toCircle.circleDegree = degree γ :=
  γ.toCircle.circleDegree_eq_degree γ fun t ↦ (γ.toCircle_unitToCircle t).symm

/-- The circle map `w ↦ z * w ^ n` has degree `n`. -/
@[simp]
theorem _root_.ContinuousMap.circleDegree_freeLoopHomotopyEquiv_symm (p : ℤ × Circle) :
    (freeLoopHomotopyEquiv.symm p).circleDegree = p.1 :=
  circleDegree_powLoop p

/-- A loop `γ` at `x`, read as a circle map, goes to its degree and its base point. -/
@[simp]
theorem freeLoopHomotopyEquiv_toCircle {x : Circle} (γ : Path x x) :
    freeLoopHomotopyEquiv γ.toCircle = (degree γ, x) := by
  simp [freeLoopHomotopyEquiv_apply]

/-- The disjoint union of copies of the circle indexed by the degree is homotopy equivalent to the
free loop space of the circle: the copy of index `m` goes to the loops `w ↦ z * w ^ m`. -/
def sigmaFreeLoopHomotopyEquiv : ContinuousMap.HomotopyEquiv (Σ _ : ℤ, Circle) C(Circle, Circle) :=
  (Homeomorph.sigmaEquivProd ℤ Circle).toHomotopyEquiv.trans freeLoopHomotopyEquiv.symm

/-- The copy of index `m` goes to the loops `w ↦ z * w ^ m`. -/
@[simp]
theorem sigmaFreeLoopHomotopyEquiv_apply (p : Σ _ : ℤ, Circle) (w : Circle) :
    sigmaFreeLoopHomotopyEquiv p w = p.2 * w ^ p.1 := by
  simp [sigmaFreeLoopHomotopyEquiv, ContinuousMap.HomotopyEquiv.trans]

/-- The inclusion `z ↦ (w ↦ z * w ^ m)` of the circle into the loops of degree `m`. -/
def freeLoopComponentInclusion (m : ℤ) : C(Circle, C(Circle, Circle)) :=
  ⟨fun z ↦ freeLoopHomotopyEquiv.symm (m, z),
    freeLoopHomotopyEquiv.symm.continuous.comp (Continuous.prodMk_right m)⟩

/-- `Circle.freeLoopComponentInclusion m` sends `z` to the loop `w ↦ z * w ^ m`. -/
@[simp]
theorem freeLoopComponentInclusion_apply (m : ℤ) (z w : Circle) :
    freeLoopComponentInclusion m z w = z * w ^ m :=
  freeLoopHomotopyEquiv_symm_apply (m, z) w

/-- The loop `w ↦ z * w ^ m` has degree `m`. -/
@[simp]
theorem _root_.ContinuousMap.circleDegree_freeLoopComponentInclusion (m : ℤ) (z : Circle) :
    (freeLoopComponentInclusion m z).circleDegree = m :=
  circleDegree_powLoop (m, z)

/-- `Circle.freeLoopComponentInclusion m` lands in the loops of degree `m`: the loop
`w ↦ z * w ^ m` goes to `(m, z)` under `Circle.freeLoopHomotopyEquiv`. -/
@[simp]
theorem freeLoopHomotopyEquiv_freeLoopComponentInclusion (m : ℤ) (z : Circle) :
    freeLoopHomotopyEquiv (freeLoopComponentInclusion m z) = (m, z) :=
  freeLoopHomotopyEquiv_apply_symm_apply (m, z)

end Circle
