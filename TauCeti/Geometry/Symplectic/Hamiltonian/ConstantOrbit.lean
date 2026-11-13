/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
public import TauCeti.Geometry.Symplectic.Hamiltonian.TimeDependent
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import TauCeti.Analysis.Normed.Operator.Exponential

/-!
# Nondegenerate constant orbits of small autonomous Hamiltonians

Let `(V, ω)` be a symplectic vector space and `F : V → ℝ` a `C²` function, with the convention
`ι_{X_F} ω = dF`. A critical point `p` of `F` is a rest point of the Hamiltonian vector field
`X_{εF} = ε X_F` for every `ε`, so its orbit is constant and `p` is a fixed point of every time map
of the Hamiltonian evolution of the autonomous Hamiltonian `εF`. This file decides when this fixed
point is nondegenerate, which is the nondegeneracy required of the generators of a Hamiltonian
Floer complex.

Write `A = dX_F(p)`. Along the constant orbit the linearized Hamiltonian equation `ζ' = ε A ζ` has
constant coefficients, so its propagator is an exponential: the derivative at `p` of the evolution
of `εF` from time `s` to time `t` is `exp ((t - s) ε A)`
(`SymplecticForm.fderiv_timeDependentHamiltonianFlow_const_mul`), by
`TauCeti.dysonSeriesLeft_const`. Contracting `A` with `ω` gives the Hessian,
`ω(A u, v) = d²F(p)(u, v)`, so `A` has the same kernel as the Hessian
(`SymplecticForm.fderiv_hamiltonianVectorField_apply_eq_zero_iff`).

* A vector annihilated by the Hessian is annihilated by `A`, hence fixed by `exp ((t - s) ε A)`.
  So a nondegenerate fixed point comes from a nondegenerate critical point, for every `ε`, `s` and
  `t` (`SymplecticForm.isNondegenerateCriticalPoint_of_isNondegenerateFixedPt`).
* Conversely, if `ε (t - s) ≠ 0` and `|ε (t - s)| ‖A‖ < log 2`, the fixed vectors of
  `exp ((t - s) ε A)` are exactly the kernel of `A`
  (`ContinuousLinearMap.exp_apply_eq_self_iff`). In this range the fixed point is nondegenerate
  exactly when `p` is a nondegenerate critical point of `F`
  (`SymplecticForm.isNondegenerateFixedPt_timeDependentHamiltonianFlow_const_mul_iff`).

The smallness is necessary. For `F = π (x² + y²)` on `ℝ²` the critical point `0` is nondegenerate,
but the time-one map of `F` is a full rotation, the identity, and every fixed point is degenerate.

The threshold is uniform over a compact set, since `‖dX_F‖` is bounded there. For every compact
`C ⊆ V` there is `ε₀ > 0` such that for `0 < |ε| < ε₀` the constant orbit of `εF` at a critical
point `p ∈ C` is a nondegenerate fixed point of the time-one map exactly when `p` is a
nondegenerate critical point of `F`
(`SymplecticForm.exists_pos_forall_isNondegenerateFixedPt_timeDependentHamiltonianFlow_iff`). This
is the step of the comparison between Hamiltonian Floer theory and Morse theory for a `C²`-small
Morse Hamiltonian `εF` which shows that the constant orbits at the critical points are admissible
generators. That the constant orbits are the only one-periodic orbits is a separate statement
(Yorke's period bound), and the index `μ = ind(F) - n` of these generators is not computed here.

The evolution is the global time-dependent Hamiltonian flow
`TauCeti.SymplecticForm.timeDependentHamiltonianFlow`, so a globally Lipschitz Hamiltonian vector
field is assumed, as for that flow. The target is a symplectic vector space, the local model of a
symplectic manifold at a critical point; the manifold statement is not proved here.

## Main results

* `SymplecticForm.fderiv_timeDependentHamiltonianFlow_const_mul`: at a critical point `p`, the
  derivative of the evolution of `εF` from `s` to `t` is `exp ((t - s) ε dX_F(p))`.
* `SymplecticForm.isNondegenerateCriticalPoint_of_isNondegenerateFixedPt`: a nondegenerate constant
  orbit sits at a nondegenerate critical point, for every `ε`.
* `SymplecticForm.isNondegenerateFixedPt_timeDependentHamiltonianFlow_const_mul_iff`: for
  `ε (t - s) ≠ 0` and `|ε (t - s)| ‖dX_F(p)‖ < log 2`, the constant orbit is nondegenerate exactly
  at a nondegenerate critical point.
* `SymplecticForm.exists_pos_forall_isNondegenerateFixedPt_timeDependentHamiltonianFlow_iff`: the
  uniform statement for the time-one maps of `εF` over a compact set of critical points.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. **120** (1989),
  575–611, on `C²`-small Hamiltonians whose one-periodic orbits are the critical points.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on the Floer complex of a small Morse function.
-/

public section

open Function NormedSpace
open scoped NNReal Manifold

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V) {F : V → ℝ} {p : V}

/-- At a critical point of `F` the Hamiltonian vector field of `εF` vanishes, so the constant curve
is an integral curve. -/
private theorem hasDerivAt_const_hamiltonianVectorField_const_mul (hp : fderiv ℝ F p = 0)
    (ε r : ℝ) : HasDerivAt (fun _ : ℝ ↦ p) (ω.hamiltonianVectorField (fun y ↦ ε * F y) p) r := by
  rw [ω.hamiltonianVectorField_const_mul, (ω.hamiltonianVectorField_eq_zero_iff F p).2 hp,
    smul_zero]
  exact hasDerivAt_const r p

/-- **The linearized evolution at a critical point.** If `p` is a critical point of a `C²`
function `F`, the derivative at `p` of the Hamiltonian evolution of `εF` from time `s` to time `t`
is `exp ((t - s) ε dX_F(p))`: along the constant orbit at `p` the linearized Hamiltonian equation
has the constant coefficient `ε dX_F(p)`. -/
theorem fderiv_timeDependentHamiltonianFlow_const_mul (hF : ContDiff ℝ 2 F)
    (hp : fderiv ℝ F p = 0) (ε : ℝ) {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension fun _ y ↦ ε * F y)) (s t : ℝ) :
    fderiv ℝ (ω.timeDependentHamiltonianFlow (fun _ y ↦ ε * F y) hX s t) p =
      exp (((t - s) * ε) • fderiv ℝ (ω.hamiltonianVectorField F) p) := by
  have hεX : ω.hamiltonianVectorField (fun y ↦ ε * F y) = ε • ω.hamiltonianVectorField F :=
    funext fun y ↦ ω.hamiltonianVectorField_const_mul ε F y
  rw [ω.fderiv_timeDependentHamiltonianFlow_eq_dysonSeriesLeft hX
    (contDiff_const.mul (hF.comp contDiff_snd))
    (ω.hasDerivAt_const_hamiltonianVectorField_const_mul hp ε), hεX, fderiv_const_smul_field,
    dysonSeriesLeft_const, Pi.smul_apply, smul_smul]

/-- The constant orbit at a critical point of `F` is fixed by every time map of the evolution of
`εF`. -/
theorem isFixedPt_timeDependentHamiltonianFlow_const_mul (hp : fderiv ℝ F p = 0) (ε : ℝ)
    {K : ℝ≥0} (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension fun _ y ↦ ε * F y))
    (s t : ℝ) : IsFixedPt (ω.timeDependentHamiltonianFlow (fun _ y ↦ ε * F y) hX s t) p := by
  exact (ω.eq_timeDependentHamiltonianFlow _ hX
    (ω.hasDerivAt_const_hamiltonianVectorField_const_mul hp ε) s t).symm

/-- The constant orbit at a critical point of `F` is a nondegenerate fixed point of the evolution
of `εF` from `s` to `t` exactly when `exp ((t - s) ε dX_F(p))` fixes no nonzero vector. -/
private theorem isNondegenerateFixedPt_timeDependentHamiltonianFlow_const_mul_iff_exp
    (hF : ContDiff ℝ 2 F)
    (hp : fderiv ℝ F p = 0) (ε : ℝ) {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension fun _ y ↦ ε * F y)) (s t : ℝ) :
    IsNondegenerateFixedPt 𝓘(ℝ, V)
        (ω.timeDependentHamiltonianFlow (fun _ y ↦ ε * F y) hX s t) p ↔
      ∀ v, exp (((t - s) * ε) • fderiv ℝ (ω.hamiltonianVectorField F) p) v = v → v = 0 := by
  have hD := (ω.differentiable_timeDependentHamiltonianFlow hX
    (contDiff_const.mul (hF.comp contDiff_snd)) s t p).hasFDerivAt.hasMFDerivAt
  rw [isNondegenerateFixedPt_iff, hD.mfderiv,
    ω.fderiv_timeDependentHamiltonianFlow_const_mul hF hp ε hX s t]
  simp only [ω.isFixedPt_timeDependentHamiltonianFlow_const_mul hp ε hX s t,
    hD.mdifferentiableAt, true_and]
  -- The tangent space `TangentSpace 𝓘(ℝ, V) p` is `V` by definition.
  exact Iff.rfl

/-- **A nondegenerate constant orbit sits at a nondegenerate critical point.** If the constant
orbit at a critical point `p` of a `C²` function `F` is a nondegenerate fixed point of the
evolution of `εF` from some time `s` to some time `t`, then `p` is a nondegenerate critical point of
`F`. No smallness is needed: a vector in the kernel of the Hessian is in the kernel of `dX_F(p)`,
and is therefore fixed by `exp ((t - s) ε dX_F(p))`. -/
theorem isNondegenerateCriticalPoint_of_isNondegenerateFixedPt (hF : ContDiff ℝ 2 F)
    (hp : fderiv ℝ F p = 0) {ε : ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension fun _ y ↦ ε * F y)) {s t : ℝ}
    (h : IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (fun _ y ↦ ε * F y) hX s t) p) :
    IsNondegenerateCriticalPoint F p := by
  refine isNondegenerateCriticalPoint_iff_separatingLeft.2
    ⟨hF.contDiffAt, hp, fun u hu ↦ ?_⟩
  have hA : fderiv ℝ (ω.hamiltonianVectorField F) p u = 0 :=
    (ω.fderiv_hamiltonianVectorField_apply_eq_zero_iff
      ((hF.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero p) u).2 hu
  refine (ω.isNondegenerateFixedPt_timeDependentHamiltonianFlow_const_mul_iff_exp hF hp ε hX s t).1
    h u ?_
  exact ContinuousLinearMap.exp_apply_of_apply_eq_zero (by rw [_root_.smul_apply, hA, smul_zero])

/-- **Constant orbits of small Hamiltonians.** Let `p` be a critical point of a `C²` function `F`,
and let `ε (t - s) ≠ 0` with `|ε (t - s)| ‖dX_F(p)‖ < log 2`. Then the constant orbit at `p` is a
nondegenerate fixed point of the evolution of `εF` from time `s` to time `t` exactly when `p` is a
nondegenerate critical point of `F`. -/
theorem isNondegenerateFixedPt_timeDependentHamiltonianFlow_const_mul_iff (hF : ContDiff ℝ 2 F)
    (hp : fderiv ℝ F p = 0) {ε : ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension fun _ y ↦ ε * F y)) {s t : ℝ}
    (hε : ε * (t - s) ≠ 0)
    (hsmall : |ε * (t - s)| * ‖fderiv ℝ (ω.hamiltonianVectorField F) p‖ < Real.log 2) :
    IsNondegenerateFixedPt 𝓘(ℝ, V)
        (ω.timeDependentHamiltonianFlow (fun _ y ↦ ε * F y) hX s t) p ↔
      IsNondegenerateCriticalPoint F p := by
  refine ⟨ω.isNondegenerateCriticalPoint_of_isNondegenerateFixedPt hF hp hX, fun h ↦ ?_⟩
  rw [ω.isNondegenerateFixedPt_timeDependentHamiltonianFlow_const_mul_iff_exp hF hp ε hX s t]
  intro v hv
  have hB : ‖((t - s) * ε) • fderiv ℝ (ω.hamiltonianVectorField F) p‖ < Real.log 2 := by
    rwa [norm_smul, Real.norm_eq_abs, mul_comm (t - s)]
  rw [ContinuousLinearMap.exp_apply_eq_self_iff hB, _root_.smul_apply,
    smul_eq_zero, mul_comm (t - s)] at hv
  exact h.separatingLeft v
    ((ω.fderiv_hamiltonianVectorField_apply_eq_zero_iff
      ((hF.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero p) v).1
      (hv.resolve_left hε))

/-- **Small multiples of a function have nondegenerate constant orbits at its nondegenerate
critical points, uniformly on compact sets.** For a `C²` function `F` and a compact set `C`, there
is `ε₀ > 0` such that for every `ε` with `0 < |ε| < ε₀` and every critical point `p ∈ C` of `F`,
the constant orbit at `p` is a nondegenerate fixed point of the time-one map of the Hamiltonian
evolution of `εF` exactly when `p` is a nondegenerate critical point of `F`. -/
theorem exists_pos_forall_isNondegenerateFixedPt_timeDependentHamiltonianFlow_iff
    (hF : ContDiff ℝ 2 F) {C : Set V} (hC : IsCompact C) :
    ∃ ε₀ > 0, ∀ ε : ℝ, 0 < |ε| → |ε| < ε₀ → ∀ {K : ℝ≥0}
      (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension fun _ y ↦ ε * F y)),
      ∀ p ∈ C, fderiv ℝ F p = 0 →
        (IsNondegenerateFixedPt 𝓘(ℝ, V)
            (ω.timeDependentHamiltonianFlow (fun _ y ↦ ε * F y) hX 0 1) p ↔
          IsNondegenerateCriticalPoint F p) := by
  -- `‖dX_F‖` is bounded on `C`, since `X_F` is `C¹`.
  have hcont : Continuous (fderiv ℝ (ω.hamiltonianVectorField F)) :=
    (ω.contDiff_hamiltonianVectorField (n := 1)
      (by simpa only [one_add_one_eq_two] using hF)).continuous_fderiv one_ne_zero
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  have hM' : 0 < |M| + 1 := by positivity
  refine ⟨Real.log 2 / (|M| + 1), div_pos (Real.log_pos one_lt_two) hM',
    fun ε hε0 hε K hX p hpC hp ↦ ?_⟩
  refine ω.isNondegenerateFixedPt_timeDependentHamiltonianFlow_const_mul_iff hF hp hX
    (by simpa using hε0.ne') ?_
  rw [sub_zero, mul_one]
  calc |ε| * ‖fderiv ℝ (ω.hamiltonianVectorField F) p‖ ≤ |ε| * (|M| + 1) :=
        mul_le_mul_of_nonneg_left ((hM p hpC).trans ((le_abs_self M).trans (by linarith)))
          (abs_nonneg ε)
    _ < Real.log 2 := (lt_div_iff₀ hM').1 hε

end TauCeti.SymplecticForm
