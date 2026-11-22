/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.MapCLM
public import TauCeti.Analysis.Normed.Lp.ProdLp
public import TauCeti.Analysis.Normed.Operator.MethodOfContinuity
public import TauCeti.Analysis.Sobolev.Circle.LinearODE.Eigenbasis

/-!
# The orbit-torus operator on the nonconstant modes along the circle factor

Let `γ` be a closed orbit of the suspension flow of a surface diffeomorphism and `C = S¹ × γ` its
orbit torus in `S¹ × Y_φ`. In a unitary trivialization of the normal bundle, the normal operator of
`C` is independent of the circle coordinate `s`,

`D u = ∂s u + A u`,  `A ζ = J₀ (ζ' - S ζ)`,

where the asymptotic operator `A` acts on loops in the coordinate `t` of period `T`, `J₀` is the
complex structure of the fibre `F` (multiplication by `I`) and `S` is a loop of real-linear maps.
In the convention `J₀ ∂t + S₀(t)` of `TauCeti.orbitTorusOperator`, `A` is the operator of the loop
`S = J₀ S₀`, and `S` is infinitesimally symplectic for `Im ⟪·, ·⟫` exactly when `S₀` is symmetric;
then `A` is symmetric (`TauCeti.CircleSobolev.real_inner_I_smul_loopOperator_comm`). The four real
sign characters of the torus twist `D`. For the two twisted along the circle factor, `D` acts on
maps antiperiodic of antiperiod `ℓ` in `s`; for the two untwisted along it, on maps periodic of
period `ℓ` in `s`. This file realizes `D`, on maps periodic in `t`, on the modes of nonzero
frequency along `s`, on Sobolev spaces, and proves that it is invertible there, along the whole
path to the complex-linear operator `∂s + J₀ ∂t`. This covers the maps antiperiodic in `s`, and the
part of the maps periodic in `s` orthogonal to the `s`-independent mode, which is treated in
`TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.PeriodicSobolev`.

**The spaces.** Such a map expands in the modes `cos (ωₖ s)` and `sin (ωₖ s)`, `k ∈ ℕ`:
`u = ∑ₖ cos (ωₖ s) aₖ + sin (ωₖ s) bₖ`, with `aₖ, bₖ` loops in `t`. The frequencies are
`ωₖ = (2k + 1)π/ℓ` for maps antiperiodic in `s` and `ωₖ = 2(k + 1)π/ℓ` for the nonconstant modes
of maps periodic in `s`; all that is used is a positive lower bound `ω₀ ≤ |ωₖ|`. The Sobolev space
`H¹` is `TauCeti.torusModeSobolev F ω`: pairs `(x₁, x₂)` of square-summable sequences with
`x₁ k = (aₖ, bₖ)` in `H¹(F)²` and `x₂ k = ωₖ (aₖ, bₖ)` in `H⁰(F)²`, so that the norm is equivalent
to `(∑ₖ ‖aₖ‖²_{H¹} + ‖bₖ‖²_{H¹} + ωₖ² (‖aₖ‖²_{H⁰} + ‖bₖ‖²_{H⁰}))^(1/2)`. The loop spaces `H^s(F)`
are the Fourier-coefficient Sobolev spaces `TauCeti.CircleSobolev`. The target is the `L²` space of
mode sequences in `H⁰(F)²`. Both carry the complex structure of `F`.

**The operator.** Since `∂s cos (ωs) = -ω sin (ωs)` and `∂s sin (ωs) = ω cos (ωs)`, the operator
acts on the mode `k` by `(aₖ, bₖ) ↦ (A aₖ + ωₖ bₖ, A bₖ - ωₖ aₖ)`
(`TauCeti.torusModeOperator`, `TauCeti.torusModeOperator_apply_apply_eq`). It depends
continuously on `S` (`TauCeti.continuous_torusModeOperator`), and for `S = 0` it is complex linear
(`TauCeti.torusModeOperator_zero_apply_smul`,
`TauCeti.exists_restrictScalars_eq_torusModeOperator_zero`).

**The estimate.** By the symmetry of `A` the cross terms cancel and each mode satisfies
`‖A a + ω b‖² + ‖A b - ω a‖² = ‖A a‖² + ‖A b‖² + ω² (‖a‖² + ‖b‖²)`, the operator counterpart of
`D* D = -∂s² + A²`. Since `|ωₖ| ≥ ω₀`, this controls the `H⁰` norms, then the `H¹` norms through
the estimate `‖a‖_{H¹} ≲ ‖A a‖ + ‖a‖_{H⁰}` for `A`. So `‖x‖ ≤ C ‖D x‖` with a constant depending
only on `T`, `ω₀` and a bound for `S` (`TauCeti.exists_forall_norm_le_mul_norm_torusModeOperator`).

**Invertibility.** For `S = 0` each mode decouples, in the variables `a ± J₀ b`, into the
operators `J₀ (ζ' ∓ ω ζ)`, which are bijections `H¹ → H⁰`; so `∂s + J₀ ∂t` is onto
(`TauCeti.surjective_torusModeOperator_zero`). Along `τ ↦ ∂s + J₀ (∂t - τ S)`, `τ ∈ [0, 1]`, every
loop `τ S` is infinitesimally symplectic and bounded by `S`, so the estimate is uniform and the
method of continuity makes every operator of the path invertible
(`TauCeti.isInvertible_torusModeOperator`). For maps antiperiodic in `s` this is the invertible
homotopy to a complex-linear reference operator along which the determinant line of an anti-`s`
twisted orbit-torus operator is oriented (`TauCeti.isInvertible_torusModeOperator_antiperiodic`);
for maps periodic in `s` it splits off the nonconstant modes as an invertible summand
(`TauCeti.isInvertible_torusModeOperator_periodic`).

The twist along `γ` by the sign `-1` is not treated here: a map antiperiodic in `t` of period `T`
is `exp (J₀ π t / T)` times a periodic one, and the corresponding loop operator is that of a
different loop. Finite covers of the torus are not treated either.

## Main definitions

* `TauCeti.torusModeSobolev F ω`: the Sobolev space `H¹` of maps with the frequencies `ω` along
  `s`, in modes.
* `TauCeti.torusModeOperator T ω S`: the operator `∂s + J₀ (∂t - S)` on it.

## Main results

* `TauCeti.exists_forall_norm_le_mul_norm_torusModeOperator`: the a priori estimate.
* `TauCeti.surjective_torusModeOperator_zero`, `TauCeti.torusModeOperator_zero_apply_smul`,
  `TauCeti.exists_restrictScalars_eq_torusModeOperator_zero`: the reference operator `∂s + J₀ ∂t`
  is onto and complex linear.
* `TauCeti.continuous_torusModeOperator`: continuity in the loop.
* `TauCeti.isInvertible_torusModeOperator`: invertibility for every infinitesimally symplectic
  loop, with its cases `TauCeti.isInvertible_torusModeOperator_antiperiodic` and
  `TauCeti.isInvertible_torusModeOperator_periodic`.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893.
* D. Salamon, *Lectures on Floer homology*, in Symplectic Geometry and Topology,
  IAS/Park City Math. Ser. 7 (1999), Section 2, for the operator `∂s + A` with `A` self-adjoint.
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 5.2, for the method of continuity.
-/

public section

noncomputable section

open Complex
open scoped Real ENNReal lp

namespace TauCeti

open CircleSobolev

/-- The product of the two mode spaces carrying `TauCeti.torusModeSobolev`. -/
local notation "𝕏[" F "]" => ℓ²(ℕ, WithLp 2 (CircleSobolev 1 F × CircleSobolev 1 F)) ×
  ℓ²(ℕ, WithLp 2 (CircleSobolev 0 F × CircleSobolev 0 F))

/-- The `L²` space of mode sequences, the target of `TauCeti.torusModeOperator`. -/
local notation "𝕐[" F "]" => ℓ²(ℕ, WithLp 2 (CircleSobolev 0 F × CircleSobolev 0 F))

section Space

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

variable (F) in
/-- The Sobolev space `H¹` of maps `u(s, t)` periodic in `t` with the frequencies `ω` along `s`,
written in the modes `u = ∑ₖ cos (ωₖ s) aₖ(t) + sin (ωₖ s) bₖ(t)`. An element is a pair `(x₁, x₂)`
of square-summable sequences, `x₁ k = (aₖ, bₖ)` in `H¹(F)²` and `x₂ k = ωₖ (aₖ, bₖ)` in `H⁰(F)²`,
so that its norm is equivalent to
`(∑ₖ ‖aₖ‖²_{H¹} + ‖bₖ‖²_{H¹} + ωₖ² (‖aₖ‖²_{H⁰} + ‖bₖ‖²_{H⁰}))^(1/2)`, the Fourier-series form of
the `H¹` norm of `u` on the torus. For `ωₖ = (2k + 1)π/ℓ` these are the maps antiperiodic of
antiperiod `ℓ` in `s`; for `ωₖ = 2(k + 1)π/ℓ`, the maps periodic of period `ℓ` in `s` with no
`s`-independent part. -/
def torusModeSobolev (ω : ℕ → ℝ) : Submodule ℂ 𝕏[F] where
  carrier := {x | ∀ k : ℕ, x.2 k = ω k •
    (inclusion zero_le_one).withLpProdMap 2 (inclusion zero_le_one) (x.1 k)}
  add_mem' {x y} hx hy k := by
    simp only [Prod.fst_add, Prod.snd_add, lp.coeFn_add, Pi.add_apply, map_add, smul_add, hx k,
      hy k]
  zero_mem' k := by
    simp only [Prod.fst_zero, Prod.snd_zero, lp.coeFn_zero, Pi.zero_apply, map_zero, smul_zero]
  smul_mem' c x hx k := by
    simp only [Prod.smul_fst, Prod.smul_snd, lp.coeFn_smul, Pi.smul_apply, map_smul, hx k]
    exact smul_comm _ _ _

/-- Membership in `TauCeti.torusModeSobolev`: the second component is `ωₖ` times the first, read
in `H⁰(F)²`. -/
theorem mem_torusModeSobolev_iff {ω : ℕ → ℝ} {x : 𝕏[F]} :
    x ∈ torusModeSobolev F ω ↔ ∀ k : ℕ, x.2 k = ω k •
      (inclusion zero_le_one).withLpProdMap 2 (inclusion zero_le_one) (x.1 k) :=
  Iff.rfl

/-- The first component of the mode `k` of the second sequence of an element of
`TauCeti.torusModeSobolev` is `ωₖ aₖ`, read in `H⁰(F)`. -/
theorem fst_snd_apply_of_mem_torusModeSobolev {ω : ℕ → ℝ} {x : 𝕏[F]}
    (hx : x ∈ torusModeSobolev F ω) (k : ℕ) :
    (x.2 k).fst = ω k • inclusion zero_le_one (x.1 k).fst := by
  simpa using congrArg WithLp.fst (hx k)

/-- The second component of the mode `k` of the second sequence of an element of
`TauCeti.torusModeSobolev` is `ωₖ bₖ`, read in `H⁰(F)`. -/
theorem snd_snd_apply_of_mem_torusModeSobolev {ω : ℕ → ℝ} {x : 𝕏[F]}
    (hx : x ∈ torusModeSobolev F ω) (k : ℕ) :
    (x.2 k).snd = ω k • inclusion zero_le_one (x.1 k).snd := by
  simpa using congrArg WithLp.snd (hx k)

/-- `TauCeti.torusModeSobolev` is closed, as an intersection of equalizers of continuous maps. -/
theorem isClosed_torusModeSobolev (ω : ℕ → ℝ) :
    IsClosed (torusModeSobolev F ω : Set 𝕏[F]) := by
  have : (torusModeSobolev F ω : Set 𝕏[F]) = ⋂ k : ℕ, {x | x.2 k = ω k •
      (inclusion zero_le_one).withLpProdMap 2 (inclusion zero_le_one) (x.1 k)} := by
    ext x
    simp [mem_torusModeSobolev_iff]
  rw [this]
  exact isClosed_iInter fun k ↦ isClosed_eq
    ((lp.evalCLM ℂ _ 2 k).continuous.comp continuous_snd)
    ((continuous_const_smul _).comp
      (((inclusion zero_le_one).withLpProdMap 2 (inclusion zero_le_one)).continuous.comp
        ((lp.evalCLM ℂ _ 2 k).continuous.comp continuous_fst)))

/-- The Sobolev space `H¹` of maps with the frequencies `ω` along `s` is complete. -/
instance [CompleteSpace F] (ω : ℕ → ℝ) : CompleteSpace (torusModeSobolev F ω) :=
  (isClosed_torusModeSobolev ω).completeSpace_coe

end Space

section Operator

variable (T : ℝ) [hT : Fact (0 < T)] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- A finite-dimensional complex space is complete, as the Sobolev spaces below need. -/
local instance instCompleteSpaceTorusModeOperator : CompleteSpace F :=
  FiniteDimensional.completeSpace ℂ F

/-- The orbit-torus operator `∂s + A` on maps with the frequencies `ω` along `s`, for the
asymptotic operator `A ζ = J₀ (ζ' - S ζ)` of a loop `S`, as a bounded real-linear map from the
Sobolev space `H¹` of these maps (`TauCeti.torusModeSobolev`) to the corresponding `L²` space of
mode sequences in `H⁰(F)²`. On the mode `cos (ωₖ s) aₖ + sin (ωₖ s) bₖ` it acts by
`(aₖ, bₖ) ↦ (A aₖ + ωₖ bₖ, A bₖ - ωₖ aₖ)` (`TauCeti.torusModeOperator_apply_apply_eq`). -/
def torusModeOperator (ω : ℕ → ℝ) (S : C(AddCircle T, F →L[ℝ] F)) :
    torusModeSobolev F ω →L[ℝ] 𝕐[F] :=
  (lp.ampliation ℕ 2 ((I • loopOperator T S).withLpProdMap 2 (I • loopOperator T S)) ∘L
      ContinuousLinearMap.fst ℝ _ _ +
    lp.ampliation ℕ 2 ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap ∘L
      ((WithLp.sndL 2 ℝ (CircleSobolev 0 F) (CircleSobolev 0 F)).prod
        (-WithLp.fstL 2 ℝ (CircleSobolev 0 F) (CircleSobolev 0 F)))) ∘L
      ContinuousLinearMap.snd ℝ _ _) ∘L
    (torusModeSobolev F ω).subtypeL.restrictScalars ℝ

/-- The operator acts on the mode `k` by `((a, b), (y₁, y₂)) ↦ (A a + y₂, A b - y₁)`, where
`(y₁, y₂) = ωₖ (a, b)` in `TauCeti.torusModeSobolev`. -/
@[simp]
theorem torusModeOperator_apply_apply (ω : ℕ → ℝ) (S : C(AddCircle T, F →L[ℝ] F))
    (x : torusModeSobolev F ω) (k : ℕ) :
    torusModeOperator T ω S x k =
      WithLp.toLp 2 (I • loopOperator T S ((x : 𝕏[F]).1 k).fst + ((x : 𝕏[F]).2 k).snd,
        I • loopOperator T S ((x : 𝕏[F]).1 k).snd - ((x : 𝕏[F]).2 k).fst) := by
  simp [torusModeOperator, sub_eq_add_neg, ← WithLp.toLp_add]

/-- The operator acts on the mode `k` by `(aₖ, bₖ) ↦ (A aₖ + ωₖ bₖ, A bₖ - ωₖ aₖ)`, where
`(aₖ, bₖ)` is the mode `k` of the first sequence of `TauCeti.torusModeSobolev`. -/
theorem torusModeOperator_apply_apply_eq (ω : ℕ → ℝ) (S : C(AddCircle T, F →L[ℝ] F))
    (x : torusModeSobolev F ω) (k : ℕ) :
    torusModeOperator T ω S x k = WithLp.toLp 2
      (I • loopOperator T S ((x : 𝕏[F]).1 k).fst + ω k • inclusion zero_le_one ((x : 𝕏[F]).1 k).snd,
        I • loopOperator T S ((x : 𝕏[F]).1 k).snd -
          ω k • inclusion zero_le_one ((x : 𝕏[F]).1 k).fst) := by
  rw [torusModeOperator_apply_apply, fst_snd_apply_of_mem_torusModeSobolev x.property,
    snd_snd_apply_of_mem_torusModeSobolev x.property]

/-- **The reference operator is complex linear.** For `S = 0` the operator `∂s + J₀ ∂t` commutes
with multiplication by complex scalars, the complex structure of `H¹` and `L²` acting by `J₀`. -/
theorem torusModeOperator_zero_apply_smul (ω : ℕ → ℝ) (c : ℂ) (x : torusModeSobolev F ω) :
    torusModeOperator T ω 0 (c • x) = c • torusModeOperator T ω 0 x := by
  refine lp.ext (funext fun k ↦ ?_)
  rw [lp.coeFn_smul, Pi.smul_apply, torusModeOperator_apply_apply,
    torusModeOperator_apply_apply]
  refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_) <;>
    simp [smul_comm c I, smul_add, smul_sub]

/-- **The reference operator as a complex-linear map.** For `S = 0` the operator `∂s + J₀ ∂t` is
the restriction of scalars of a bounded complex-linear map, for the complex structures of `H¹` and
`L²` given by `J₀`. -/
theorem exists_restrictScalars_eq_torusModeOperator_zero (ω : ℕ → ℝ) :
    ∃ L : torusModeSobolev F ω →L[ℂ] 𝕐[F], L.restrictScalars ℝ = torusModeOperator T ω 0 :=
  ⟨{ toFun := torusModeOperator T ω 0
     map_add' := map_add _
     map_smul' := torusModeOperator_zero_apply_smul T ω
     cont := (torusModeOperator T ω 0).continuous }, rfl⟩

/-- **Continuous dependence on the loop.** The operator `∂s + A` on maps with the frequencies `ω`
along `s` depends continuously, in operator norm, on the loop `S` with its uniform norm. -/
theorem continuous_torusModeOperator (ω : ℕ → ℝ) :
    Continuous (torusModeOperator (F := F) T ω) := by
  have hpair : Continuous fun S : C(AddCircle T, F →L[ℝ] F) ↦
      (I • loopOperator T S).withLpProdMap 2 (I • loopOperator T S) := by
    refine (LipschitzWith.of_dist_le_mul (K := 1)
      (f := fun f : CircleSobolev 1 F →L[ℝ] CircleSobolev 0 F ↦ f.withLpProdMap 2 f)
      fun f g ↦ ?_).continuous.comp ((continuous_loopOperator T).const_smul I)
    rw [dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.withLpProdMap_sub,
      ContinuousLinearMap.norm_withLpProdMap, max_self, NNReal.coe_one, one_mul]
  exact ((((lp.ampliation ℕ 2).continuous.comp hpair).clm_comp continuous_const).add
    continuous_const).clm_comp continuous_const

end Operator

section Inner

variable (T : ℝ) [hT : Fact (0 < T)] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- A finite-dimensional complex space is complete, as the Sobolev spaces below need. -/
local instance instCompleteSpaceTorusModeSobolev : CompleteSpace F :=
  FiniteDimensional.completeSpace ℂ F

/-! ### One mode -/

/-- **The energy identity of one mode.** For an infinitesimally symplectic loop `S`, the
asymptotic operator `A = J₀ (d/dt - S)` is symmetric, so the cross terms cancel in
`‖A a + ω b‖² + ‖A b - ω a‖² = ‖A a‖² + ‖A b‖² + ω² (‖a‖² + ‖b‖²)`, the norms of `a, b` being taken
in `H⁰`. -/
private theorem norm_sq_add_norm_sq_mode (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) (ω : ℝ)
    (a b : CircleSobolev 1 F) :
    ‖I • loopOperator T S a + ω • inclusion zero_le_one b‖ ^ 2 +
        ‖I • loopOperator T S b - ω • inclusion zero_le_one a‖ ^ 2 =
      ‖loopOperator T S a‖ ^ 2 + ‖loopOperator T S b‖ ^ 2 +
        ω ^ 2 * (‖inclusion (E := F) zero_le_one a‖ ^ 2 +
          ‖inclusion (E := F) zero_le_one b‖ ^ 2) := by
  rw [norm_add_sq_real, norm_sub_sq_real, real_inner_smul_right, real_inner_smul_right,
    real_inner_comm (inclusion zero_le_one a), ← real_inner_I_smul_loopOperator_comm T S hS a b,
    norm_smul, norm_smul, norm_smul, norm_smul, norm_I]
  simp only [mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- **The estimate of one mode.** If `‖S t‖ ≤ M` for every `t` and `ω₀ ≤ |ω|` with `ω₀ > 0`, the
`H¹` norms of `a, b` are bounded by the mode `(A a + ω b, A b - ω a)` of the operator, with a
constant depending only on `T`, `M` and `ω₀`. -/
private theorem norm_sq_add_norm_sq_le_mode (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) {M ω₀ ω : ℝ}
    (hM : ∀ t, ‖S t‖ ≤ M) (hω₀ : 0 < ω₀) (hω : ω₀ ≤ |ω|) (a b : CircleSobolev 1 F) :
    ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ ((2 + 4 * (T / (2 * π)) ^ 2 * M ^ 2) / ω₀ ^ 2 + 4 * (T / (2 * π)) ^ 2) *
      (‖I • loopOperator T S a + ω • inclusion zero_le_one b‖ ^ 2 +
        ‖I • loopOperator T S b - ω • inclusion zero_le_one a‖ ^ 2) := by
  rw [norm_sq_add_norm_sq_mode T S hS]
  set c := T / (2 * π) with hc
  set p := ‖inclusion (E := F) zero_le_one a‖ ^ 2 + ‖inclusion (E := F) zero_le_one b‖ ^ 2
  set q := ‖loopOperator T S a‖ ^ 2 + ‖loopOperator T S b‖ ^ 2
  -- Each `H¹` norm is controlled by `A` and the `H⁰` norm.
  have hab (d : CircleSobolev 1 F) : ‖d‖ ^ 2 ≤ (2 + 4 * c ^ 2 * M ^ 2) *
      ‖inclusion (E := F) zero_le_one d‖ ^ 2 + 4 * c ^ 2 * ‖loopOperator T S d‖ ^ 2 := by
    have h := norm_sq_le_of_loopOperator T hM d
    rw [← hc] at h
    set ι := ‖inclusion (E := F) zero_le_one d‖
    set L := ‖loopOperator T S d‖
    have h1 : (L + M * ι) ^ 2 ≤ 2 * L ^ 2 + 2 * M ^ 2 * ι ^ 2 := by
      nlinarith [sq_nonneg (L - M * ι)]
    have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * c ^ 2 by positivity)
    linarith
  have hp : p ≤ (q + ω ^ 2 * p) / ω₀ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have : ω₀ ^ 2 ≤ ω ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ hω₀.le hω 2
    nlinarith [show 0 ≤ p by positivity, show 0 ≤ q by positivity]
  have hq : q ≤ q + ω ^ 2 * p := le_add_of_nonneg_right (by positivity)
  calc ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ (2 + 4 * c ^ 2 * M ^ 2) * p + 4 * c ^ 2 * q := by
        linarith [hab a, hab b]
    _ ≤ (2 + 4 * c ^ 2 * M ^ 2) * ((q + ω ^ 2 * p) / ω₀ ^ 2) + 4 * c ^ 2 * (q + ω ^ 2 * p) := by
        gcongr
    _ = _ := by ring

/-! ### The a priori estimate -/

/-- The constant of the a priori estimate of `TauCeti.torusModeOperator` on a mode, for frequencies
of absolute value at least `ω₀` and loops of uniform norm at most `M`. -/
private def modeConstant (ω₀ M : ℝ) : ℝ :=
  (2 + 4 * (T / (2 * π)) ^ 2 * M ^ 2) / ω₀ ^ 2 + 4 * (T / (2 * π)) ^ 2

/-- The a priori estimate of one mode `y = (a, b)` of frequency `ω`, `ω₀ ≤ |ω|`: both `y` in
`H¹(F)²` and `ω y` in `H⁰(F)²` are bounded by the mode `z = (A a + ω b, A b - ω a)` of the
operator. -/
private theorem norm_le_mode {ω₀ : ℝ} (hω₀ : 0 < ω₀) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) {M ω : ℝ}
    (hM : ∀ t, ‖S t‖ ≤ M) (hω : ω₀ ≤ |ω|)
    {y : WithLp 2 (CircleSobolev 1 F × CircleSobolev 1 F)}
    {z : WithLp 2 (CircleSobolev 0 F × CircleSobolev 0 F)}
    (hz₁ : I • loopOperator T S y.fst + ω • inclusion zero_le_one y.snd = z.fst)
    (hz₂ : I • loopOperator T S y.snd - ω • inclusion zero_le_one y.fst = z.snd) :
    ‖y‖ ≤ √(modeConstant T ω₀ M) * ‖z‖ ∧
      ‖ω • (inclusion zero_le_one).withLpProdMap 2 (inclusion zero_le_one) y‖ ≤ ‖z‖ := by
  have hz : ‖z‖ ^ 2 = ‖I • loopOperator T S y.fst + ω • inclusion zero_le_one y.snd‖ ^ 2 +
      ‖I • loopOperator T S y.snd - ω • inclusion zero_le_one y.fst‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, hz₁, hz₂]
  have hK : 0 ≤ modeConstant T ω₀ M := by unfold modeConstant; positivity
  constructor
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, Real.sq_sqrt hK, hz, WithLp.prod_norm_sq_eq_of_L2]
    unfold modeConstant
    exact norm_sq_add_norm_sq_le_mode T S hS hM hω₀ hω _ _
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [hz, norm_sq_add_norm_sq_mode T S hS, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      WithLp.prod_norm_sq_eq_of_L2]
    simp only [ContinuousLinearMap.withLpProdMap_apply, WithLp.toLp_fst, WithLp.toLp_snd]
    nlinarith [sq_nonneg ‖loopOperator T S y.fst‖, sq_nonneg ‖loopOperator T S y.snd‖]

/-- The a priori estimate of `TauCeti.torusModeOperator`, mode by mode. -/
private theorem norm_apply_le_mode {ω : ℕ → ℝ} {ω₀ : ℝ} (hω₀ : 0 < ω₀) (hω : ∀ k, ω₀ ≤ |ω k|)
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) {M : ℝ}
    (hM : ∀ t, ‖S t‖ ≤ M) (x : torusModeSobolev F ω) (k : ℕ) :
    ‖(x : 𝕏[F]).1 k‖ ≤ √(modeConstant T ω₀ M) * ‖torusModeOperator T ω S x k‖ ∧
      ‖(x : 𝕏[F]).2 k‖ ≤ ‖torusModeOperator T ω S x k‖ := by
  have hD := torusModeOperator_apply_apply_eq T ω S x k
  rw [mem_torusModeSobolev_iff.1 x.property k]
  exact norm_le_mode T hω₀ S hS hM (hω k) (congrArg WithLp.fst hD).symm
    (congrArg WithLp.snd hD).symm

/-- **The a priori estimate.** Let the frequencies satisfy `ω₀ ≤ |ωₖ|` for some `ω₀ > 0`. For a
bound `M`, there is a constant `C` such that `‖x‖ ≤ C ‖(∂s + A) x‖` for every `x` in the Sobolev
space `H¹` of maps with the frequencies `ω` along `s`, for the asymptotic operator `A` of every
infinitesimally symplectic loop `S` with `‖S t‖ ≤ M` for all `t`. In particular `∂s + A` is
injective with closed range. -/
theorem exists_forall_norm_le_mul_norm_torusModeOperator {ω : ℕ → ℝ} {ω₀ : ℝ} (hω₀ : 0 < ω₀)
    (hω : ∀ k, ω₀ ≤ |ω k|) (M : ℝ) :
    ∃ C, ∀ S : C(AddCircle T, F →L[ℝ] F),
      (∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) → (∀ t, ‖S t‖ ≤ M) →
        ∀ x, ‖x‖ ≤ C * ‖torusModeOperator T ω S x‖ := by
  refine ⟨√(modeConstant T ω₀ M) + 1, fun S hS hM x ↦ ?_⟩
  have hx₁ : ‖(x : 𝕏[F]).1‖ ≤ √(modeConstant T ω₀ M) * ‖torusModeOperator T ω S x‖ := by
    rw [← abs_of_nonneg (Real.sqrt_nonneg (modeConstant T ω₀ M)), ← Real.norm_eq_abs, ← norm_smul]
    refine lp.norm_mono two_ne_zero fun k ↦ ?_
    rw [lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (norm_apply_le_mode T hω₀ hω S hS hM x k).1
  have hx₂ : ‖(x : 𝕏[F]).2‖ ≤ ‖torusModeOperator T ω S x‖ :=
    lp.norm_mono two_ne_zero fun k ↦ (norm_apply_le_mode T hω₀ hω S hS hM x k).2
  rw [← Submodule.norm_coe, Prod.norm_def, add_mul, one_mul]
  exact max_le (hx₁.trans (le_add_of_nonneg_right (norm_nonneg _)))
    (hx₂.trans (le_add_of_nonneg_left (by positivity)))

/-! ### The complex-linear reference operator -/

/-- **The modes of the reference operator are onto.** For `S = 0` and `ω ≠ 0` every pair
`(z₁, z₂)` in `H⁰(F)²` is `(J₀ a' + ω b, J₀ b' - ω a)` for some `a, b ∈ H¹(F)`: in the variables
`u = a + J₀ b` and `v = a - J₀ b` the equations decouple into `J₀ (u' - ω u) = z₁ + J₀ z₂` and
`J₀ (v' + ω v) = z₁ - J₀ z₂`, and `ζ ↦ ζ' ± ω ζ` is a bijection `H¹ → H⁰`. -/
private theorem exists_mode_eq_of_zero {ω : ℝ} (hω : ω ≠ 0) (z₁ z₂ : CircleSobolev 0 F) :
    ∃ a b : CircleSobolev 1 F, I • loopOperator T 0 a + ω • inclusion zero_le_one b = z₁ ∧
      I • loopOperator T 0 b - ω • inclusion zero_le_one a = z₂ := by
  obtain ⟨u, hu⟩ := (bijective_derivative_add_smul_inclusion (E := F) T
    (show (0 : ℝ) + 1 = 1 by norm_num) (c := ((-ω : ℝ) : ℂ)) (by simpa using hω)).2
      ((-I) • (z₁ + I • z₂))
  obtain ⟨v, hv⟩ := (bijective_derivative_add_smul_inclusion (E := F) T
    (show (0 : ℝ) + 1 = 1 by norm_num) (c := (ω : ℂ)) (by simpa using hω)).2
      ((-I) • (z₁ - I • z₂))
  simp only [add_apply, smul_apply] at hu hv
  refine ⟨(1 / 2 : ℂ) • (u + v), (I / 2) • (v - u), ?_, ?_⟩ <;>
  · simp only [loopOperator_zero, ContinuousLinearMap.coe_restrictScalars', map_add, map_sub,
      map_smul, ← Complex.coe_smul]
    rw [eq_sub_of_add_eq hu, eq_sub_of_add_eq hv]
    -- Compare the coefficients of `z₁`, `z₂`, `u` and `v`, which agree since `I ^ 2 = -1`.
    match_scalars <;> grind [I_sq]

/-- **The reference operator is onto.** Let the frequencies satisfy `ω₀ ≤ |ωₖ|` for some `ω₀ > 0`.
For `S = 0` the operator `∂s + J₀ ∂t` maps the Sobolev space `H¹` of maps with the frequencies `ω`
along `s` onto the corresponding `L²` space. -/
theorem surjective_torusModeOperator_zero {ω : ℕ → ℝ} {ω₀ : ℝ} (hω₀ : 0 < ω₀)
    (hω : ∀ k, ω₀ ≤ |ω k|) :
    Function.Surjective (torusModeOperator (F := F) T ω 0) := by
  intro z
  choose a b hab using fun k : ℕ ↦
    exists_mode_eq_of_zero T (abs_pos.1 (hω₀.trans_le (hω k))) (z k).fst (z k).snd
  have hzero : ∀ t v w, (inner ℂ ((0 : C(AddCircle T, F →L[ℝ] F)) t v) w).im +
      (inner ℂ v ((0 : C(AddCircle T, F →L[ℝ] F)) t w)).im = 0 := by simp
  -- The mode estimate for `S = 0` puts the solutions in `H¹`, with square-summable norms.
  have hmode (k : ℕ) := norm_le_mode T hω₀ 0 hzero (M := 0) (fun _ ↦ by simp)
    (hω k) (y := WithLp.toLp 2 (a k, b k)) (hab k).1 (hab k).2
  have h₁ (k : ℕ) : ‖WithLp.toLp 2 (a k, b k)‖ ≤ ‖(√(modeConstant T ω₀ 0) • ⇑z) k‖ := by
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (hmode k).1
  set x₁ : ℓ²(ℕ, WithLp 2 (CircleSobolev 1 F × CircleSobolev 1 F)) :=
    ⟨fun k ↦ WithLp.toLp 2 (a k, b k), ((lp.memℓp z).const_smul _).mono' h₁⟩
  have h₂ (k : ℕ) : ‖ω k •
      (inclusion zero_le_one).withLpProdMap 2 (inclusion zero_le_one) (x₁ k)‖ ≤ ‖z k‖ :=
    (hmode k).2
  set x₂ : ℓ²(ℕ, WithLp 2 (CircleSobolev 0 F × CircleSobolev 0 F)) :=
    ⟨fun k ↦ ω k • (inclusion zero_le_one).withLpProdMap 2 (inclusion zero_le_one) (x₁ k),
      (lp.memℓp z).mono' h₂⟩
  refine ⟨⟨(x₁, x₂), fun k ↦ rfl⟩, lp.ext (funext fun k ↦ ?_)⟩
  rw [torusModeOperator_apply_apply]
  refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_)
  · simpa [x₁, x₂] using (hab k).1
  · simpa [x₁, x₂] using (hab k).2

/-! ### Invertibility -/

/-- **Invertibility along the homotopy to the complex-linear reference.** Let the frequencies
satisfy `ω₀ ≤ |ωₖ|` for some `ω₀ > 0`. For every infinitesimally symplectic loop `S`, the
orbit-torus operator `∂s + A`, `A ζ = J₀ (ζ' - S ζ)`, is invertible from the Sobolev space `H¹` of
maps with the frequencies `ω` along `s` onto the corresponding `L²` space. Since `τ • S` is again
infinitesimally symplectic, every operator of the path `τ ↦ ∂s + J₀ (∂t - τ S)`, `τ ∈ [0, 1]`, is
invertible; the path is continuous (`TauCeti.continuous_torusModeOperator`) and starts at the
complex-linear operator `∂s + J₀ ∂t` (`TauCeti.torusModeOperator_zero_apply_smul`). -/
theorem isInvertible_torusModeOperator {ω : ℕ → ℝ} {ω₀ : ℝ} (hω₀ : 0 < ω₀)
    (hω : ∀ k, ω₀ ≤ |ω k|) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (torusModeOperator T ω S).IsInvertible := by
  -- The method of continuity along `τ ↦ τ • S`, from the a priori estimate, uniform along the
  -- path, and surjectivity at `τ = 0`.
  obtain ⟨C, hC⟩ := exists_forall_norm_le_mul_norm_torusModeOperator (F := F) T hω₀ hω ‖S‖
  have hL : ContinuousOn (fun τ : ℝ ↦ torusModeOperator T ω (τ • S)) (Set.Icc 0 1) :=
    ((continuous_torusModeOperator T ω).comp (continuous_id.smul continuous_const)).continuousOn
  have hτ (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (t : AddCircle T) : ‖(τ • S) t‖ ≤ ‖S‖ := by
    rw [ContinuousMap.smul_apply, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul (abs_le.2 ⟨by linarith [hτ.1], hτ.2⟩) (S.norm_coe_le_norm t)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have h0 : Function.Surjective (torusModeOperator T ω ((0 : ℝ) • S)) := by
    rw [zero_smul ℝ S]
    exact surjective_torusModeOperator_zero T hω₀ hω
  have h := isPreconnected_Icc.isInvertible_of_forall_norm_le hL
    (fun τ hτ' x ↦ hC (τ • S) (inner_smul_apply_im_add_inner_smul_apply_im_eq_zero T S hS τ)
      (hτ τ hτ') x)
    (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) h0
  rwa [one_smul ℝ S] at h

/-! ### Maps antiperiodic or periodic along the circle factor -/

/-- The frequency `π / |ℓ|` bounds every frequency `c π / ℓ` with `1 ≤ c`, in particular the
antiperiodic frequencies `(2k + 1)π/ℓ` and the nonzero periodic frequencies `2(k + 1)π/ℓ`. -/
private theorem div_le_abs_mul_div {ℓ : ℝ} (hℓ : ℓ ≠ 0) {c : ℝ} (hc : 1 ≤ c) :
    π / |ℓ| ≤ |c * π / ℓ| := by
  rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ c * π)]
  have := abs_pos.2 hℓ
  gcongr
  nlinarith [Real.pi_pos]

/-- **The orbit-torus operator on maps antiperiodic in `s`.** For `ℓ ≠ 0` and every
infinitesimally symplectic loop `S`, the operator `∂s + A` on the maps antiperiodic of antiperiod
`ℓ` in `s`, whose frequencies are `ωₖ = (2k + 1)π/ℓ`, is invertible. This holds along the whole
path `τ ↦ ∂s + J₀ (∂t - τ S)` to the complex-linear operator `∂s + J₀ ∂t`, which is the reference
for the orientation of the determinant lines of the two orbit-torus operators twisted along the
circle factor. -/
theorem isInvertible_torusModeOperator_antiperiodic {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (torusModeOperator T (fun k : ℕ ↦ (2 * k + 1) * π / ℓ) S).IsInvertible :=
  isInvertible_torusModeOperator T (div_pos Real.pi_pos (abs_pos.2 hℓ))
    (fun k ↦ div_le_abs_mul_div hℓ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])) S hS

/-- **The orbit-torus operator on the nonconstant modes of maps periodic in `s`.** For `ℓ ≠ 0` and
every infinitesimally symplectic loop `S`, the operator `∂s + A` on the maps periodic of period
`ℓ` in `s` with no `s`-independent part, whose frequencies are `ωₖ = 2(k + 1)π/ℓ`, is invertible.
So on maps periodic in `s` the operator is determined, up to an invertible summand, by the
asymptotic operator `A` acting on the `s`-independent mode. -/
theorem isInvertible_torusModeOperator_periodic {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (torusModeOperator T (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) S).IsInvertible :=
  isInvertible_torusModeOperator T (div_pos Real.pi_pos (abs_pos.2 hℓ))
    (fun k ↦ div_le_abs_mul_div hℓ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])) S hS

end Inner

end TauCeti
