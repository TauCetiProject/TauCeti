/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Additivity
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FreeLoop.Basic
public import TauCeti.Topology.PathSpace.Moore.Comparison.FreeLoop

/-!
# The homotopy type and the homology of the free loop space of the circle

The free loop space `𝓛S¹ = C(S¹, S¹)` of the circle, with the compact-open topology, is homotopy
equivalent to the disjoint union `Σ n : ℤ, S¹ ≅ ℤ × S¹` of circles indexed by the integers
(`Circle.freeLoopHomotopyEquiv`): a free loop `f` goes to its degree `n` and its value `f 1`, and
`(n, w)` goes back to the free loop `z ↦ w zⁿ`. So each path component
of `𝓛S¹`, the free loops of a fixed degree (`Circle.freeLoopComponentsEquivInt`), is homotopy
equivalent to a circle, by evaluation at `1`.

The homotopy from a free loop `f` of degree `n` to `z ↦ f(1) zⁿ` comes from lifting the whole
family of loops `t ↦ f(e^{2πit}) f(1)⁻¹`, `f ∈ 𝓛S¹`, through the universal covering
`exp : ℝ → S¹` with Mathlib's homotopy lifting `IsCoveringMap.liftHomotopy`. This gives an angle
function `θ(t, f)` jointly continuous in `t` and `f` (`Circle.freeLoopAngle`), with
`θ(0, f) = 0` and `θ(1, f) = 2πn`. Interpolating linearly between `θ(t, f)` and `2πnt` moves `f`
to `z ↦ f(1) zⁿ` through free loops. In particular the degree `θ(1, f) / 2π` is continuous in
`f` (`Circle.continuous_degree_toBasedLoop`).

Consequently the singular homology of `𝓛S¹`, with coefficients in any object `R` of an abelian
category with exact coproducts indexed by `ℤ`, is a coproduct of copies of the homology of the
circle, one for each degree (`Circle.freeLoopSingularHomologyIso`):

`H_k(𝓛S¹; R) ≅ ∐_{n ∈ ℤ} H_k(S¹; R)`.

It vanishes in degrees `k ≥ 2` (`Circle.isZero_freeLoopSingularHomology`). The same holds for the
Moore free loop space, which is homotopy equivalent to `C(S¹, S¹)`
(`Circle.mooreFreeLoopSingularHomologyIso`, `Circle.isZero_mooreFreeLoopSingularHomology`). With
integer coefficients, since `H₀(S¹; ℤ)` and `H₁(S¹; ℤ)` are infinite cyclic, this describes the
right-hand side of the Viterbo isomorphism `SH_k(T*S¹) ≅ H_k(𝓛S¹; ℤ)` for the circle: a direct sum
of copies of `ℤ` indexed by the degree, that is, a copy of `ℤ[ℤ]`, in degrees `0` and `1`, and zero
in degrees `k ≥ 2`.

## Main declarations

* `Circle.freeLoopAngle`: the continuous angle function of the family of free loops.
* `Circle.continuous_degree_toBasedLoop`: the degree is continuous on `C(S¹, S¹)`.
* `Circle.freeLoopHomotopyEquiv`: `C(S¹, S¹) ≃ₕ Σ n : ℤ, S¹`.
* `Circle.freeLoopSingularHomologyIso`: `H_k(C(S¹, S¹); R) ≅ ∐_{n ∈ ℤ} H_k(S¹; R)`.
* `Circle.isZero_freeLoopSingularHomology`: `H_k(C(S¹, S¹); R) = 0` for `k ≥ 2`.
* `Circle.mooreFreeLoopSingularHomologyIso`, `Circle.isZero_mooreFreeLoopSingularHomology`: the
  same for the Moore free loop space.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 1.30.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4 (the Viterbo isomorphism for `T*S¹`).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology TauCeti unitInterval

namespace Circle

/-! ### The angle function of the free loops -/

/-- The family of loops `t ↦ f(e^{2πit}) f(1)⁻¹` at `1`, parametrized by the free loops `f`. -/
private def freeLoopRatio : C(I × C(Circle, Circle), Circle) :=
  ⟨fun p ↦ p.2 (unitToCircle p.1) * (p.2 1)⁻¹, by fun_prop⟩

/-- **The angle function of the free loops of the circle.** The lift `θ(t, f)` of the family of
loops `t ↦ f(e^{2πit}) f(1)⁻¹` through `Circle.exp : ℝ → S¹` starting at `θ(0, f) = 0`. It is
jointly continuous in `t` and in the free loop `f`. -/
def freeLoopAngle : C(I × C(Circle, Circle), ℝ) :=
  isCoveringMap_exp.liftHomotopy freeLoopRatio (.const _ 0) fun f ↦ by
    simp [freeLoopRatio]

@[simp]
theorem exp_freeLoopAngle (t : I) (f : C(Circle, Circle)) :
    exp (freeLoopAngle (t, f)) = f (unitToCircle t) * (f 1)⁻¹ :=
  congr_fun (isCoveringMap_exp.liftHomotopy_lifts _ _ _) (t, f)

@[simp]
theorem freeLoopAngle_zero (f : C(Circle, Circle)) : freeLoopAngle (0, f) = 0 :=
  isCoveringMap_exp.liftHomotopy_zero _ _ _ f

/-- The angle function sweeps `2π` times the degree of the free loop. -/
theorem freeLoopAngle_one (f : C(Circle, Circle)) :
    freeLoopAngle (1, f) = degree f.toBasedLoop * (2 * Real.pi) := by
  have h := sub_eq_degree_mul f.toBasedLoop
    (θ := fun t ↦ freeLoopAngle (t, f) + (f 1 : ℂ).arg) (by fun_prop) fun t ↦ by
      rw [exp_add, exp_freeLoopAngle, exp_arg, inv_mul_cancel_right,
        ContinuousMap.toBasedLoop_apply]
  rw [freeLoopAngle_zero, zero_add] at h
  linarith

/-- **The degree is continuous on the free loop space**, that is, locally constant: it is the
angle swept by the continuous angle function, divided by `2π`. -/
@[fun_prop]
theorem continuous_degree_toBasedLoop :
    Continuous fun f : C(Circle, Circle) ↦ degree f.toBasedLoop := by
  rw [Int.isClosedEmbedding_coe_real.isEmbedding.continuous_iff]
  have h : ((↑) : ℤ → ℝ) ∘ (fun f : C(Circle, Circle) ↦ degree f.toBasedLoop) =
      fun f ↦ freeLoopAngle (1, f) / (2 * Real.pi) := by
    ext f
    rw [Function.comp_apply, freeLoopAngle_one, mul_div_cancel_right₀ _ (by positivity)]
  rw [h]
  fun_prop

/-! ### The homotopy equivalence `C(S¹, S¹) ≃ₕ Σ n : ℤ, S¹` -/

/-- A free loop goes to its degree and its value at `1`. -/
private def freeLoopToSigma : C(C(Circle, Circle), Σ _ : ℤ, Circle) :=
  ⟨fun f ↦ ⟨degree f.toBasedLoop, f 1⟩, by
    have h : Continuous fun q : ℤ × Circle ↦ (⟨q.1, q.2⟩ : Σ _ : ℤ, Circle) :=
      continuous_prod_of_discrete_left.2 fun n ↦ @continuous_sigmaMk ℤ (fun _ ↦ Circle) _ n
    exact h.comp (continuous_degree_toBasedLoop.prodMk (continuous_eval_const 1))⟩

/-- The free loop `z ↦ w zⁿ`, as a continuous function of `(n, w)`. -/
private def freeLoopOfSigma : C(Σ _ : ℤ, Circle, C(Circle, Circle)) :=
  ⟨fun p ↦ ⟨fun z ↦ p.2 * z ^ p.1, by fun_prop⟩,
    continuous_sigma fun n ↦ ContinuousMap.continuous_of_continuous_uncurry _
      (by exact continuous_fst.mul ((continuous_zpow n).comp continuous_snd))⟩

private theorem freeLoopToSigma_apply (f : C(Circle, Circle)) :
    freeLoopToSigma f = ⟨degree f.toBasedLoop, f 1⟩ :=
  (rfl)

private theorem freeLoopOfSigma_apply (p : Σ _ : ℤ, Circle) (z : Circle) :
    freeLoopOfSigma p z = p.2 * z ^ p.1 :=
  (rfl)

/-- The free loop `z ↦ w zⁿ` has degree `n` and value `w` at `1`. -/
private theorem freeLoopToSigma_freeLoopOfSigma (p : Σ _ : ℤ, Circle) :
    freeLoopToSigma (freeLoopOfSigma p) = p := by
  obtain ⟨n, w⟩ := p
  have h : degree (freeLoopOfSigma ⟨n, w⟩).toBasedLoop = n := by
    refine degree_eq_of_sub_eq _ (θ := fun t ↦ (w : ℂ).arg + n * (2 * Real.pi * t))
      (by fun_prop) (fun t ↦ ?_) (by simp)
    rw [exp_add, exp_arg, exp_intCast_mul, ContinuousMap.toBasedLoop_apply, freeLoopOfSigma_apply,
      unitToCircle_apply]
  rw [freeLoopToSigma_apply, h, freeLoopOfSigma_apply, one_zpow, mul_one]

/-- The straight-line interpolation, at time `s`, between the angle `2πnt` of `z ↦ zⁿ`, for `n`
the degree of a free loop `f`, and the angle function `θ(t, f)` of `f`, rotated to start at
`f 1`. -/
private def freeLoopHomotopyAux : C((I × C(Circle, Circle)) × I, Circle) :=
  ⟨fun q ↦ q.1.2 1 * exp ((1 - q.1.1) * (degree q.1.2.toBasedLoop * (2 * Real.pi * q.2)) +
    q.1.1 * freeLoopAngle (q.2, q.1.2)), by
    have hdeg : Continuous fun q : (I × C(Circle, Circle)) × I ↦
        (degree q.1.2.toBasedLoop : ℝ) :=
      continuous_of_discreteTopology.comp (continuous_degree_toBasedLoop.comp (by fun_prop))
    exact (by fun_prop : Continuous fun q : (I × C(Circle, Circle)) × I ↦ q.1.2 1).mul
      (exp.continuous.comp (by fun_prop))⟩

private theorem freeLoopHomotopyAux_apply (s : I) (f : C(Circle, Circle)) (t : I) :
    freeLoopHomotopyAux ((s, f), t) = f 1 * exp ((1 - s) *
      (degree f.toBasedLoop * (2 * Real.pi * t)) + s * freeLoopAngle (t, f)) :=
  (rfl)

/-- The interpolated angle sweeps `2π` times the degree, so each interpolated path closes up. -/
private theorem freeLoopHomotopyAux_zero_eq_one (p : I × C(Circle, Circle)) :
    freeLoopHomotopyAux (p, 0) = freeLoopHomotopyAux (p, 1) := by
  obtain ⟨s, f⟩ := p
  simp only [freeLoopHomotopyAux_apply, Set.Icc.coe_one, Set.Icc.coe_zero, freeLoopAngle_zero,
    freeLoopAngle_one, mul_zero, mul_one, add_zero, exp_zero]
  rw [← add_mul, sub_add_cancel, one_mul, mul_comm (degree _ : ℝ), exp_two_pi_mul_int, mul_one]

/-- The interpolated angles of `freeLoopHomotopyAux`, as closed paths on the unit interval. -/
private def freeLoopHomotopyPath : C(I × C(Circle, Circle), ClosedUnitPath Circle) :=
  ⟨fun p ↦ ⟨freeLoopHomotopyAux.curry p, freeLoopHomotopyAux_zero_eq_one p⟩,
    freeLoopHomotopyAux.curry.continuous.subtype_mk _⟩

private theorem freeLoopHomotopyPath_apply (p : I × C(Circle, Circle)) (t : I) :
    (freeLoopHomotopyPath p).1 t = freeLoopHomotopyAux (p, t) :=
  (rfl)

/-- The homotopy `(s, f) ↦ (e^{2πit} ↦ f(1) e^{i((1 - s) 2πnt + s θ(t, f))})` from
`z ↦ f(1) zⁿ` to `f`, for `n` the degree of `f`. -/
private def freeLoopHomotopy : C(I × C(Circle, Circle), C(Circle, Circle)) :=
  ⟨fun p ↦ circleMapHomeomorphClosedUnitPath.symm (freeLoopHomotopyPath p),
    circleMapHomeomorphClosedUnitPath.symm.continuous.comp freeLoopHomotopyPath.continuous⟩

private theorem freeLoopHomotopy_apply (p : I × C(Circle, Circle)) :
    freeLoopHomotopy p = circleMapHomeomorphClosedUnitPath.symm (freeLoopHomotopyPath p) :=
  (rfl)

private theorem freeLoopHomotopy_unitToCircle (s : I) (f : C(Circle, Circle)) (t : I) :
    freeLoopHomotopy (s, f) (unitToCircle t) = f 1 * exp ((1 - s) *
      (degree f.toBasedLoop * (2 * Real.pi * t)) + s * freeLoopAngle (t, f)) := by
  rw [freeLoopHomotopy_apply, circleMapHomeomorphClosedUnitPath_symm_unitToCircle,
    freeLoopHomotopyPath_apply, freeLoopHomotopyAux_apply]

/-- **The free loop space of the circle is homotopy equivalent to a disjoint union of circles
indexed by `ℤ`**, that is, to `ℤ × S¹`: a free loop goes to its degree `n` and its value at `1`,
and `(n, w)` goes back to the free loop `z ↦ w zⁿ`. -/
def freeLoopHomotopyEquiv : ContinuousMap.HomotopyEquiv C(Circle, Circle) (Σ _ : ℤ, Circle) where
  toFun := freeLoopToSigma
  invFun := freeLoopOfSigma
  left_inv := ⟨{
    toContinuousMap := freeLoopHomotopy
    map_zero_left f := ContinuousMap.ext fun z ↦ by
      obtain ⟨t, rfl⟩ := unitToCircle_surjective z
      rw [ContinuousMap.toFun_eq_coe, freeLoopHomotopy_unitToCircle]
      rw [ContinuousMap.comp_apply, freeLoopToSigma_apply, freeLoopOfSigma_apply,
        unitToCircle_apply, ← exp_intCast_mul]
      simp only [Set.Icc.coe_zero, sub_zero, one_mul, zero_mul, add_zero]
    map_one_left f := ContinuousMap.ext fun z ↦ by
      obtain ⟨t, rfl⟩ := unitToCircle_surjective z
      rw [ContinuousMap.toFun_eq_coe, freeLoopHomotopy_unitToCircle]
      simp only [Set.Icc.coe_one, sub_self, zero_mul, one_mul, zero_add, exp_freeLoopAngle,
        ContinuousMap.id_apply]
      rw [mul_comm, inv_mul_cancel_right] }⟩
  right_inv := by
    rw [show freeLoopToSigma.comp freeLoopOfSigma = ContinuousMap.id _ from
      ContinuousMap.ext freeLoopToSigma_freeLoopOfSigma]

@[simp]
theorem freeLoopHomotopyEquiv_apply (f : C(Circle, Circle)) :
    freeLoopHomotopyEquiv f = ⟨degree f.toBasedLoop, f 1⟩ :=
  (rfl)

@[simp]
theorem freeLoopHomotopyEquiv_symm_apply (p : Σ _ : ℤ, Circle) (z : Circle) :
    freeLoopHomotopyEquiv.symm p z = p.2 * z ^ p.1 :=
  (rfl)

/-! ### Singular homology -/

variable {C : Type*} [Category C] [HasCoproducts.{0} C] [Abelian C]
  [HasExactColimitsOfShape (Discrete ℤ) C] (R : C) (k : ℕ)

/-- **The homology of the free loop space of the circle.** With coefficients in any object of an
abelian category with exact coproducts indexed by `ℤ`, `H_k(C(S¹, S¹); R)` is the coproduct, over
the degrees `n ∈ ℤ`, of copies of `H_k(S¹; R)`. -/
def freeLoopSingularHomologyIso :
    ((singularHomologyFunctor C k).obj R).obj (TopCat.of C(Circle, Circle)) ≅
      ∐ fun _ : ℤ ↦ ((singularHomologyFunctor C k).obj R).obj (TopCat.of Circle) :=
  freeLoopHomotopyEquiv.singularHomologyIso R k ≪≫
    (isColimitCofanSingularHomology (fun _ : ℤ ↦ TopCat.of Circle) C R k).coconePointUniqueUpToIso
      (colimit.isColimit _)

/-- **The free loop space of the circle has no homology in degrees `k ≥ 2`.** -/
theorem isZero_freeLoopSingularHomology {k : ℕ} (hk : 2 ≤ k) :
    IsZero (((singularHomologyFunctor C k).obj R).obj (TopCat.of C(Circle, Circle))) :=
  ((isColimitCofanSingularHomology (fun _ : ℤ ↦ TopCat.of Circle) C R k).isZero_pt
    (Functor.isZero _ fun _ ↦ isZero_singularHomology_circle_of_two_le R hk)).of_iso
      (freeLoopHomotopyEquiv.singularHomologyIso R k)

/-- **The homology of the Moore free loop space of the circle**: `H_k(𝓛S¹; R)` is the coproduct,
over the degrees `n ∈ ℤ`, of copies of `H_k(S¹; R)`. -/
def mooreFreeLoopSingularHomologyIso :
    ((singularHomologyFunctor C k).obj R).obj (TopCat.of (MooreFreeLoopSpace Circle)) ≅
      ∐ fun _ : ℤ ↦ ((singularHomologyFunctor C k).obj R).obj (TopCat.of Circle) :=
  (MooreFreeLoopSpace.homotopyEquivCircleMap Circle).singularHomologyIso R k ≪≫
    freeLoopSingularHomologyIso R k

/-- The Moore free loop space of the circle has no homology in degrees `k ≥ 2`. -/
theorem isZero_mooreFreeLoopSingularHomology {k : ℕ} (hk : 2 ≤ k) :
    IsZero (((singularHomologyFunctor C k).obj R).obj
      (TopCat.of (MooreFreeLoopSpace Circle))) :=
  (isZero_freeLoopSingularHomology R hk).of_iso
    ((MooreFreeLoopSpace.homotopyEquivCircleMap Circle).singularHomologyIso R k)

end Circle
