/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Capacity.HoferZehnder
public import TauCeti.Geometry.Symplectic.Complex.Line
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.ODE.Yorke
import TauCeti.Geometry.Symplectic.Capacity.Levels
import TauCeti.Geometry.Symplectic.CompatibleMetric
import TauCeti.Geometry.Symplectic.Hamiltonian.Hessian

/-!
# The `π₁`-sensitive capacity of a ball is at least its area

Let `V` be a nonzero finite-dimensional real inner product space with a symplectic form `ω` and an
almost complex structure `J` whose metric `ω(·, J ·)` is the inner product, such as `ℂⁿ` with its
standard symplectic form and complex structure. Every complex line through the centre of the ball
`B²ⁿ(r)` of radius `r` meets it in a disc of symplectic area `π r²`. This file proves the lower
bound

`π r² ≤ c°_HZ(U; W)`

for every set `U` containing a ball of radius `r` and every set `W` in which contractibility is
tested (`TauCeti.SymplecticForm.ofReal_pi_mul_sq_le_contractibleHZCapacity`). In particular the
ball `B` of radius `r` has `π r² ≤ c°_HZ(B)`. The Hofer–Zehnder capacity of the ball is exactly
`π r²`; the upper bound rests on an existence theorem for periodic orbits and is not proved here.
On the complex line with its standard area form this is the bound for a disc
(`TauCeti.ofReal_pi_mul_sq_le_contractibleHZCapacity`).

The lower bound comes from the squared distance `F(y) = ‖y - p‖²`. Its Hamiltonian vector field is
the infinitesimal rotation `y ↦ -2 J (y - p)` about `p`
(`TauCeti.SymplecticForm.hamiltonianVectorField_norm_sub_sq`), which is `2`-Lipschitz since `J` is
an isometry. By Yorke's theorem (`Function.Periodic.eq_const_of_hasDerivAt_of_lipschitzOnWith`) a
periodic orbit of a `2`-Lipschitz field with period `T < π` is constant. This is independent of any
contractibility, so no level of `F` carries a closed characteristic of period less than `π`,
contractible in any `W`. The level-set lower bound
`TauCeti.SmoothTwoForm.IsNondegenerate.ofReal_mul_sub_le_contractibleHZCapacity` then gives
`τ (b - a) ≤ c°_HZ(U; W)` for every `τ < π` and `0 < a < b < r²`, and letting `τ → π`, `a → 0`
and `b → r²` gives `π r²`.

The nonzero hypothesis on `V` is needed: on the zero space the ball of every radius is a point, an
admissible Hamiltonian must vanish on a nonempty open set, hence everywhere, and the capacity is
`0`.

## Main results

* `TauCeti.SymplecticForm.ofReal_pi_mul_sq_le_contractibleHZCapacity`: in a symplectic vector space
  with a compatible complex structure, a set containing a ball of radius `r` has `π₁`-sensitive
  capacity at least `π r²`, whatever set contractibility is tested in.
* `TauCeti.ofReal_pi_mul_sq_le_contractibleHZCapacity`: on the complex line with its standard area
  form, a set containing a disc of radius `r` has `π₁`-sensitive capacity at least `π r²`.

## References

* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Chapter 3 (radial Hamiltonians and the capacity of the ball).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 12.3.
* J. A. Yorke, *Periods of periodic solutions and the Lipschitz constant*, Proc. Amer. Math. Soc.
  22 (1969), 509–512.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 6.1 and the remarks after it.
-/

public section

noncomputable section

open Filter Function Metric Set Topology
open scoped RealInnerProductSpace

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- If the inner product of `V` is the metric `ω(·, J ·)`, no level `‖y - p‖² = s` of the squared
distance to `p` carries a closed characteristic of period at most `τ < π`, whatever set
contractibility is tested in: the Hamiltonian vector field `y ↦ -2 J (y - p)` is `2`-Lipschitz, so
by Yorke's theorem its periodic orbits of period less than `π` are constant. -/
private theorem not_hasContractibleClosedCharacteristicOfPeriodLE_norm_sub_sq
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (p : V) (W : Set V) (s : ℝ) {τ : ℝ} (hτ : τ < Real.pi) :
    ¬ω.constSmooth.HasContractibleClosedCharacteristicOfPeriodLE W (fun y ↦ ‖y - p‖ ^ 2) s τ := by
  -- The Hamiltonian vector field is the infinitesimal rotation `-2 J (y - p)`, which is
  -- `2`-Lipschitz because `J` is an isometry.
  have hX : LipschitzWith 2 fun y : V ↦ (-2 : ℝ) • J (y - p) :=
    LipschitzWith.of_dist_le_mul fun v w ↦ by
      rw [dist_eq_norm, dist_eq_norm, ← smul_sub, ← J.apply_sub, sub_sub_sub_cancel_right,
        norm_smul, ω.norm_apply_eq_norm_of_apply_apply_self_eq_inner (fun v ↦ hg v v)]
      norm_num
  rw [SmoothTwoForm.hasContractibleClosedCharacteristicOfPeriodLE_iff]
  rintro ⟨T, γ, hT, hTτ, hγ, hper, ⟨t, ht⟩, -⟩
  refine ht (congrFun (hper.eq_const_of_hasDerivAt_of_lipschitzOnWith hT (fun s ↦ ?_)
    hX.lipschitzOnWith ?_) t)
  · -- An integral curve of the Hamiltonian vector field solves Hamilton's equations.
    have h := hγ s
    rw [hamiltonianVectorField_constSmooth, hamiltonianVectorField_norm_sub_sq hg] at h
    exact hasDerivAt_iff_hasFDerivAt.2 (hasMFDerivAt_iff_hasFDerivAt.1 h)
  · push_cast
    linarith

/-- **The `π₁`-sensitive capacity of a ball is at least its area.** Let `V` be a nonzero
symplectic vector space whose inner product is the metric `ω(·, J ·)` of a compatible complex
structure `J`. A set `U` containing the ball of radius `r ≥ 0` about some point has
`c°_HZ(U; W) ≥ π r²`, whatever set `W` contractibility is tested in. In particular the ball `B`
of radius `r` has `c°_HZ(B) ≥ π r²`. -/
theorem ofReal_pi_mul_sq_le_contractibleHZCapacity [Nontrivial V]
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {p : V} {r : ℝ} (hr : 0 ≤ r) {W U : Set V}
    (hU : ball p r ⊆ U) :
    ENNReal.ofReal (Real.pi * r ^ 2) ≤ ω.constSmooth.contractibleHZCapacity W U := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  set F : V → ℝ := fun y ↦ ‖y - p‖ ^ 2
  have hFc : ContDiff ℝ (⊤ : ℕ∞) F := (contDiff_id.sub contDiff_const).norm_sq ℝ
  have hball : ball p r ⊆ interior U := interior_maximal hU isOpen_ball
  -- For each `t ∈ (0, 1)`, the levels of `F` in `((1 - t) r² / 2, (1 + t) r² / 2)` carry no
  -- closed characteristic of period at most `π t`, giving the bound `π t · t r² = π t² r²`.
  have hle : ∀ᶠ t in 𝓝[<] (1 : ℝ), ENNReal.ofReal (Real.pi * t ^ 2 * r ^ 2) ≤
      ω.constSmooth.contractibleHZCapacity W U := by
    filter_upwards [Ioo_mem_nhdsLT one_pos] with t ⟨ht₀, ht₁⟩
    have hR : 0 < r ^ 2 := by positivity
    have hb : (1 + t) * r ^ 2 / 2 < r ^ 2 := by nlinarith
    have hm : 0 ≤ ((1 + t) * r ^ 2 / 2 + r ^ 2) / 2 := by positivity
    -- A point of `U` at squared distance halfway between `(1 + t) r² / 2` and `r²` from `p`.
    obtain ⟨e, he⟩ := exists_norm_eq V (Real.sqrt_nonneg (((1 + t) * r ^ 2 / 2 + r ^ 2) / 2))
    convert (isNondegenerate_constSmooth ω).ofReal_mul_sub_le_contractibleHZCapacity
        (τ := Real.pi * t) (W := W) hFc.contMDiff
        (a := (1 - t) * r ^ 2 / 2) (b := (1 + t) * r ^ 2 / 2) (by nlinarith)
        ((isCompact_closedBall p √((1 + t) * r ^ 2 / 2)).of_isClosed_subset
          (isClosed_le hFc.continuous continuous_const) fun y hy ↦ ?_)
        (fun y hy ↦ hball ?_) (by simp [ModelWithCorners.interior_eq_univ])
        ⟨p, by simp only [F, sub_self, norm_zero]; nlinarith⟩ ⟨p + e, hball ?_, ?_⟩
        fun s _ ↦ not_hasContractibleClosedCharacteristicOfPeriodLE_norm_sub_sq hg p W s
          (by nlinarith [Real.pi_pos]) using 2
    · ring
    · simp only [F, mem_ofPred_eq] at hy
      rw [mem_closedBall, dist_eq_norm]
      exact Real.le_sqrt_of_sq_le hy
    · simp only [F, mem_ofPred_eq] at hy
      rw [mem_ball, dist_eq_norm]
      nlinarith [norm_nonneg (y - p)]
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, he, Real.sqrt_lt' hr]
      linarith
    · simp only [F, add_sub_cancel_left, he, Real.sq_sqrt hm]
      linarith
  refine le_of_tendsto ?_ hle
  have hc : Continuous fun t : ℝ ↦ ENNReal.ofReal (Real.pi * t ^ 2 * r ^ 2) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds

end SymplecticForm

/-- **The `π₁`-sensitive capacity of a disc is at least its area.** On the complex line with its
standard area form, a set `U` containing the disc of radius `r ≥ 0` about some point has
`c°_HZ(U; W) ≥ π r²`, whatever set `W` contractibility is tested in. In particular the disc `D` of
radius `r` has `c°_HZ(D) ≥ π r²`. -/
theorem ofReal_pi_mul_sq_le_contractibleHZCapacity {p : ℂ} {r : ℝ} (hr : 0 ≤ r) {W U : Set ℂ}
    (hU : ball p r ⊆ U) :
    ENNReal.ofReal (Real.pi * r ^ 2) ≤
      stdComplexSymplecticForm.constSmooth.contractibleHZCapacity W U :=
  SymplecticForm.ofReal_pi_mul_sq_le_contractibleHZCapacity
    stdComplexSymplecticForm_apply_ofComplexModule_eq_inner hr hU

end TauCeti
