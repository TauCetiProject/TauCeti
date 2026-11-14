/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain
public import TauCeti.Analysis.Sobolev.Circle.LinearODE.Eigenbasis
import TauCeti.Analysis.Normed.Operator.CompactFamily

/-!
# The stationary cylinder operator over periodic circle Sobolev spaces

Let `E` be a finite-dimensional complex normed space and `S : C(AddCircle T, E →L[ℝ] E)` a
continuous loop of real-linear maps of period `T > 0`. On the cylinder `ℝ × AddCircle T`, the
inclusion `ι : H¹(AddCircle T, E) →L[ℝ] H⁰(AddCircle T, E)` defines the common-domain Sobolev
graph space

`WeakDerivStep volume ⊤ 2 (ι.compLpL 2 (volume.restrict (⊤ : Opens ℝ)))`

of paths `u ∈ L²(ℝ, H¹(AddCircle T, E))` whose `H⁰`-valued path `ι ∘ u` has a weak `s`-derivative
in `L²(ℝ, H⁰(AddCircle T, E))`. Combining `ι` with the asymptotic loop operator
`I • CircleSobolev.loopOperator T S : H¹(AddCircle T, E) →L[ℝ] H⁰(AddCircle T, E)` via
`TauCeti.WeakDerivStep.domainTrajectoryOperator` produces the stationary cylinder operator

`∂s ∘ ι + I • L_S`

realized as `TauCeti.CircleSobolev.cylinderOperator T S`.

When `F` is a finite-dimensional complex inner product space and every `S t` is infinitesimally
symplectic for `ω₀(v, w) = Im ⟪v, w⟫`, `I • loopOperator T S` is `ι`-symmetric
(`TauCeti.CircleSobolev.real_inner_I_smul_loopOperator_comm`) and Fredholm of index zero
(`TauCeti.CircleSobolev.isFredholm_I_smul_loopOperator`,
`TauCeti.CircleSobolev.index_I_smul_loopOperator`). Specializing the general common-domain
trajectory theory of `TauCeti/Analysis/ODE/TrajectoryOperator/CommonDomain.lean` yields:

* **Always injective, coercive iff nondegenerate.** `cylinderOperator T S` is injective for every
  infinitesimally symplectic loop `S`, and the following are equivalent:
  1. `cylinderOperator T S` is invertible;
  2. `cylinderOperator T S` is Fredholm;
  3. `loopOperator T S` is invertible;
  4. `ζ' = S ζ` admits no nonzero continuous `T`-periodic solution `ζ`.
* **Pythagorean identity and inverse bound.** At a nondegenerate loop,
  `‖(cylinderOperator T S).inverse‖ ≤ √(1 + ‖(loopOperator T S).inverse‖²)`.
* **Exponential weight shifts and compact-family uniformity.** Subtracting the constant loop
  `δ • (I • id)` from `S` shifts the asymptotic operator by `-δ • ι` while preserving
  infinitesimal symplecticity, realizing the conjugated operator `e^{δ s} (∂s + A) e^{-δ s}` on
  exponentially weighted ends. Over any compact parameter set of nondegenerate loops and any
  continuous family of zero-order perturbations `J`, all sufficiently small weights `|δ| ≤ ε`
  remain invertible on the cylinder with a uniform operator-norm bound on the inverse.
* **Eigenmode splitting.** Along any eigenvector `I • loopOperator T S a = λ • ι a` (such as the
  Hilbert eigenbasis of `TauCeti.CircleSobolev.exists_hilbertBasis_I_smul_loopOperator_eq_smul`),
  scalar mode injection and projection intertwine `cylinderOperator T S` with the scalar
  differential expression `w' + λ w`.

## Main declarations

* `TauCeti.CircleSobolev.cylinderInclusion`: the real-linear Sobolev inclusion
  `H¹(AddCircle T, E) →L[ℝ] H⁰(AddCircle T, E)`.
* `TauCeti.CircleSobolev.cylinderOperator`: the stationary cylinder operator `∂s ∘ ι + I • L_S`.
* `TauCeti.CircleSobolev.I_smul_loopOperator_sub_smul_const_I`,
  `TauCeti.CircleSobolev.cylinderOperator_sub_smul_const_I`: exponential weight shifts `S - δ I`
  subtract `δ • ι` from the asymptotic operator.
* `TauCeti.CircleSobolev.isInvertible_cylinderOperator_iff_isInvertible_loopOperator`,
  `TauCeti.CircleSobolev.isFredholm_cylinderOperator_iff_isInvertible_loopOperator`,
  `TauCeti.CircleSobolev.isInvertible_cylinderOperator_iff`: equivalences between cylinder
  invertibility, cylinder Fredholmness, loop invertibility, and absence of periodic solutions.
* `TauCeti.CircleSobolev.norm_inverse_cylinderOperator_le`: inverse norm bound
  `√(1 + ‖(loopOperator T S).inverse‖²)`.
* `TauCeti.CircleSobolev.exists_pos_isInvertible_cylinderOperator_sub_smul_norm_inverse_le` and
  `exists_pos_isInvertible_cylinderOperator_sub_smul_of_isInvertible_loopOperator`:
  uniform weighted cylinder inverses over compact families.

## References

* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. **7** (1999), Lecture 2,
  Proposition 2.2 (invertibility of `∂s + A` on `W^{1,2}(ℝ × S¹)` iff `A` is invertible).
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33, Theorem 4.17.
-/

public section

noncomputable section

open Complex Filter _root_.MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology

namespace TauCeti.CircleSobolev

/-! ### Real-linear multiplication by `I` and the cylinder operator -/

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Multiplication by `I` on a complex normed space, viewed as a real continuous linear
equivalence. -/
private def mulIEquiv (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℂ Y] : Y ≃L[ℝ] Y :=
  (ContinuousLinearEquiv.smulLeft (R₁ := ℂ) (M₁ := Y)
    (Units.mk0 I I_ne_zero)).restrictScalars ℝ

private theorem mulIEquiv_comp {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] (L : X →L[ℝ] Y) :
    (mulIEquiv Y : Y →L[ℝ] Y).comp L = I • L := by
  ext x
  simp [mulIEquiv]

/-- The real-linear Sobolev inclusion `H¹ →L[ℝ] H⁰` serving as the slice domain embedding on a
cylinder. -/
def cylinderInclusion : CircleSobolev 1 E →L[ℝ] CircleSobolev 0 E :=
  (inclusion (E := E) zero_le_one).restrictScalars ℝ

@[simp]
theorem cylinderInclusion_apply (a : CircleSobolev 1 E) :
    cylinderInclusion a = inclusion zero_le_one a := by
  simp [cylinderInclusion]

theorem cylinderInclusion_injective : Function.Injective (cylinderInclusion (E := E)) :=
  inclusion_injective zero_le_one

variable (T : ℝ) [Fact (0 < T)] [FiniteDimensional ℂ E]

local instance : CompleteSpace E := FiniteDimensional.completeSpace ℂ E

/-- `I • loopOperator T S` is a Fredholm operator of real Banach spaces. -/
theorem isFredholm_I_smul_loopOperator (S : C(AddCircle T, E →L[ℝ] E)) :
    (I • loopOperator T S).IsFredholm := by
  rw [← mulIEquiv_comp]
  exact (isFredholm_loopOperator T S).equiv_comp (mulIEquiv _)

/-- `I • loopOperator T S` has Fredholm index zero. -/
@[simp]
theorem index_I_smul_loopOperator (S : C(AddCircle T, E →L[ℝ] E)) :
    (I • loopOperator T S).index = 0 := by
  rw [← mulIEquiv_comp, ContinuousLinearMap.index_equiv_comp, index_loopOperator]

/-- `I • loopOperator T S` is invertible if and only if `loopOperator T S` is invertible. -/
@[simp]
theorem isInvertible_I_smul_loopOperator_iff (S : C(AddCircle T, E →L[ℝ] E)) :
    (I • loopOperator T S).IsInvertible ↔ (loopOperator T S).IsInvertible := by
  rw [← mulIEquiv_comp, ContinuousLinearMap.isInvertible_equiv_comp]

/-- Multiplication by `I` is isometric on `H⁰`, so `I • loopOperator T S` and `loopOperator T S`
have equal inverse norms. -/
@[simp]
theorem norm_inverse_I_smul_loopOperator (S : C(AddCircle T, E →L[ℝ] E)) :
    ‖(I • loopOperator T S).inverse‖ = ‖(loopOperator T S).inverse‖ := by
  rw [← mulIEquiv_comp, ContinuousLinearMap.inverse_equiv_comp]
  set R := (loopOperator T S).inverse
  set e := mulIEquiv (CircleSobolev 0 E)
  refine le_antisymm
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg R) fun y ↦ ?_)
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y ↦ ?_)
  · have hy : ‖e.symm y‖ = ‖y‖ := by
      change ‖I⁻¹ • y‖ = ‖y‖
      rw [norm_smul, norm_inv, norm_I, inv_one, one_mul]
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hy] using
      R.le_opNorm (e.symm y)
  · have hy : ‖e y‖ = ‖y‖ := by
      change ‖I • y‖ = ‖y‖
      rw [norm_smul, norm_I, one_mul]
    have hcomp : (R.comp (e.symm : CircleSobolev 0 E →L[ℝ] CircleSobolev 0 E)) (e y) = R y := by
      simp
    rw [← hcomp, ← hy]
    exact (R.comp (e.symm : CircleSobolev 0 E →L[ℝ] CircleSobolev 0 E)).le_opNorm (e y)

/-- Subtracting the constant complex-structure loop `δ • (I • id)` from `S` subtracts `δ • ι` from
the asymptotic loop operator `I • loopOperator T S`. -/
theorem I_smul_loopOperator_sub_smul_const_I (S : C(AddCircle T, E →L[ℝ] E)) (δ : ℝ) :
    I • loopOperator T (S - δ • ContinuousMap.const _ (I • ContinuousLinearMap.id ℝ E)) =
      I • loopOperator T S - δ • cylinderInclusion := by
  ext a : 1
  rw [smul_apply, loopOperator_sub, add_apply, mulLoop_smul, smul_apply, mulLoop_const_smul_id,
    smul_add, sub_apply, smul_apply, smul_apply, cylinderInclusion_apply]
  rw [← Complex.coe_smul δ (I • inclusion zero_le_one a), smul_smul, smul_smul,
    show I * (δ : ℂ) * I = -(δ : ℂ) by linear_combination (δ : ℂ) * I_sq, neg_smul,
    Complex.coe_smul, sub_eq_add_neg]

/-- **The stationary cylinder operator** `∂s ∘ ι + I • L_S` from
`L²(ℝ, H¹(AddCircle T, E)) ∩ W^{1,2}(ℝ, H⁰(AddCircle T, E))` to `L²(ℝ, H⁰(AddCircle T, E))`. -/
def cylinderOperator (S : C(AddCircle T, E →L[ℝ] E)) :
    WeakDerivStep volume ⊤ 2
      (cylinderInclusion (E := E).compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) →L[ℝ]
    Lp (CircleSobolev 0 E) 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
  WeakDerivStep.domainTrajectoryOperator cylinderInclusion (I • loopOperator T S)

/-- Explicit `L²` decomposition of `cylinderOperator T S u` into its `s`-derivative and slice
components. -/
theorem cylinderOperator_apply (S : C(AddCircle T, E →L[ℝ] E))
    (u : WeakDerivStep volume ⊤ 2
      (cylinderInclusion (E := E).compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    cylinderOperator T S u =
      (ContinuousLinearMap.apply ℝ (CircleSobolev 0 E) (1 : ℝ)).compLpL 2
        (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
        (WeakDerivStep.weakFDeriv
          (cylinderInclusion.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u) +
      (I • loopOperator T S).compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
        (WeakDerivStep.prev
          (cylinderInclusion.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u) :=
  WeakDerivStep.domainTrajectoryOperator_apply _ _ u

/-- `cylinderOperator T` depends continuously in operator norm on the coefficient loop `S`. -/
@[fun_prop]
theorem continuous_cylinderOperator : Continuous (cylinderOperator (E := E) T) :=
  (WeakDerivStep.lipschitzWith_domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2)
    (cylinderInclusion (E := E))).continuous.comp
    ((continuous_loopOperator T).const_smul I)

/-- **Weighted cylinder shift.** Replacing `S` by `S - δ • const (I • id)` shifts the zero-order
part of `cylinderOperator T S` by `-δ • ι`, matching conjugation of `∂s + A` by `e^{δ s}`. -/
theorem cylinderOperator_sub_smul_const_I (S : C(AddCircle T, E →L[ℝ] E)) (δ : ℝ) :
    cylinderOperator T (S - δ • ContinuousMap.const _ (I • ContinuousLinearMap.id ℝ E)) =
      WeakDerivStep.domainTrajectoryOperator cylinderInclusion
        (I • loopOperator T S - δ • cylinderInclusion) := by
  rw [cylinderOperator, I_smul_loopOperator_sub_smul_const_I]

/-- **Uniform weighted cylinder inverses over a compact family.** If `cylinderOperator T (S p)` is
invertible for every `p` in a compact parameter set `K`, then for any continuous family `J` of
coefficient loops there is a uniform weight bound `ε > 0` and inverse bound `C ≥ 0` on `[−ε, ε]`.
No symmetry or complex-linearity hypothesis on `S` or `J` is needed once unweighted invertibility
holds. -/
theorem exists_pos_isInvertible_cylinderOperator_sub_smul_norm_inverse_le
    {P : Type*} [TopologicalSpace P] {K : Set P} (hK : IsCompact K)
    (S J : P → C(AddCircle T, E →L[ℝ] E)) (hS : ContinuousOn S K) (hJ : ContinuousOn J K)
    (hinv : ∀ p ∈ K, (cylinderOperator T (S p)).IsInvertible) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ p ∈ K, ∀ δ : ℝ, |δ| ≤ ε →
      (cylinderOperator T (S p - δ • J p)).IsInvertible ∧
        ‖(cylinderOperator T (S p - δ • J p)).inverse‖ ≤ C := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let L : K × ℝ →
      WeakDerivStep volume ⊤ 2
        (cylinderInclusion (E := E).compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) →L[ℝ]
      Lp (CircleSobolev 0 E) 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
    fun z ↦ cylinderOperator T (S z.1 - z.2 • J z.1)
  have hL : Continuous L :=
    (continuous_cylinderOperator T).comp
      ((hS.domRestrict.comp continuous_fst).sub
        (continuous_snd.smul (hJ.domRestrict.comp continuous_fst)))
  obtain ⟨V, hV, C, hC, hbound⟩ :=
    isCompact_univ.exists_mem_nhds_isInvertible_norm_inverse_le L 0
      (fun _ _ ↦ hL.continuousAt) fun p _ ↦ by
        dsimp only [L]
        rw [zero_smul ℝ (J p), sub_zero]
        exact hinv p p.2
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨r / 2, by positivity, C, hC, fun p hp δ hδ ↦ hbound ⟨p, hp⟩ (mem_univ _) δ (hrV ?_)⟩
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hδ.trans_lt (half_lt_self hr)

end Normed

/-! ### Infinitesimally symplectic loops: symmetry, invertibility, and eigenmodes -/

section Symplectic

variable (T : ℝ) {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Shifting an infinitesimally symplectic loop `S` by a real multiple of `I • id` preserves
infinitesimal symplecticity for `ω₀(v, w) = Im ⟪v, w⟫`. -/
theorem im_inner_sub_smul_const_I_add_eq_zero {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) (δ : ℝ)
    (t : AddCircle T) (v w : F) :
    (inner ℂ
        ((S - δ • ContinuousMap.const (AddCircle T) (I • ContinuousLinearMap.id ℝ F)) t v) w).im +
      (inner ℂ v
        ((S - δ • ContinuousMap.const (AddCircle T) (I • ContinuousLinearMap.id ℝ F)) t w)).im =
      0 := by
  simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.const_apply,
    sub_apply, smul_apply, ContinuousLinearMap.id_apply, inner_sub_left, inner_sub_right,
    Complex.sub_im]
  have h1 : (inner ℂ (δ • I • v) w).im = -δ * (inner ℂ v w).re := by
    rw [← Complex.coe_smul, inner_smul_left, inner_smul_left]
    simp
  have h2 : (inner ℂ v (δ • I • w)).im = δ * (inner ℂ v w).re := by
    rw [← Complex.coe_smul, inner_smul_right, inner_smul_right]
    simp
  rw [h1, h2]
  linarith [hS t v w]

variable [Fact (0 < T)] [FiniteDimensional ℂ F]

local instance : CompleteSpace F := FiniteDimensional.completeSpace ℂ F

/-- **Pythagorean identity on the cylinder.** For an infinitesimally symplectic loop `S`, the
`s`-derivative `(ι ∘ u)'` and the slice term `(I • L_S) ∘ u` are orthogonal in
`L²(ℝ, H⁰(AddCircle T, F))`. -/
theorem norm_cylinderOperator_sq {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (u : WeakDerivStep volume ⊤ 2
      (cylinderInclusion (E := F).compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    ‖cylinderOperator T S u‖ ^ 2 =
      ‖WeakDerivStep.weakFDeriv
          (cylinderInclusion.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u‖ ^ 2 +
        ‖(I • loopOperator T S).compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
          (WeakDerivStep.prev
            (cylinderInclusion.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u)‖ ^ 2 :=
  WeakDerivStep.norm_domainTrajectoryOperator_sq
    (real_inner_I_smul_loopOperator_comm T S hS) u

/-- **Injectivity on the cylinder.** For any infinitesimally symplectic loop `S` (even a degenerate
one), `cylinderOperator T S` has trivial kernel on `L²(ℝ, H¹) ∩ W^{1,2}(ℝ, H⁰)`. -/
theorem injective_cylinderOperator {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    Function.Injective (cylinderOperator T S) :=
  WeakDerivStep.injective_domainTrajectoryOperator_of_symmetric
    cylinderInclusion_injective (real_inner_I_smul_loopOperator_comm T S hS)

/-- **Invertibility equivalence: cylinder vs. loop.** For an infinitesimally symplectic loop `S`,
the stationary cylinder operator `∂s ∘ ι + I • L_S` is invertible if and only if the periodic loop
operator `L_S` is invertible. -/
theorem isInvertible_cylinderOperator_iff_isInvertible_loopOperator
    {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (cylinderOperator T S).IsInvertible ↔ (loopOperator T S).IsInvertible := by
  rw [cylinderOperator, WeakDerivStep.isInvertible_domainTrajectoryOperator_iff
    cylinderInclusion_injective (real_inner_I_smul_loopOperator_comm T S hS)
    (isFredholm_I_smul_loopOperator T S) (index_I_smul_loopOperator T S),
    isInvertible_I_smul_loopOperator_iff]

/-- **Fredholm equivalence: cylinder vs. loop.** For an infinitesimally symplectic loop `S`, the
stationary cylinder operator is Fredholm if and only if `L_S` is invertible (and hence if and only
if the cylinder operator is invertible). -/
theorem isFredholm_cylinderOperator_iff_isInvertible_loopOperator
    {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (cylinderOperator T S).IsFredholm ↔ (loopOperator T S).IsInvertible := by
  rw [cylinderOperator, WeakDerivStep.isFredholm_domainTrajectoryOperator_iff
    cylinderInclusion_injective (real_inner_I_smul_loopOperator_comm T S hS)
    (isFredholm_I_smul_loopOperator T S) (index_I_smul_loopOperator T S),
    isInvertible_I_smul_loopOperator_iff]

/-- **Classical ODE criterion for cylinder invertibility.** For an infinitesimally symplectic loop
`S`, `cylinderOperator T S` is invertible if and only if `ζ' = S ζ` has no nonzero continuous
`T`-periodic solution. -/
theorem isInvertible_cylinderOperator_iff {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (cylinderOperator T S).IsInvertible ↔
      ∀ ζ : C(AddCircle T, F), (∀ x : ℝ, HasDerivAt (fun y : ℝ ↦ ζ y) (S x (ζ x)) x) → ζ = 0 :=
  (isInvertible_cylinderOperator_iff_isInvertible_loopOperator T hS).trans
    (isInvertible_loopOperator_iff T S)

/-- When `S` is infinitesimally symplectic and `loopOperator T S` is invertible, `cylinderOperator T
S` has Fredholm index zero. -/
@[simp]
theorem index_cylinderOperator {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hL : (loopOperator T S).IsInvertible) :
    (cylinderOperator T S).index = 0 :=
  WeakDerivStep.index_domainTrajectoryOperator
    (real_inner_I_smul_loopOperator_comm T S hS)
    ((isInvertible_I_smul_loopOperator_iff T S).2 hL)

/-- **Inverse norm bound on the cylinder.** For an infinitesimally symplectic nondegenerate loop
`S`, `‖(cylinderOperator T S).inverse‖ ≤ √(1 + ‖(loopOperator T S).inverse‖²)`. -/
theorem norm_inverse_cylinderOperator_le {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hL : (loopOperator T S).IsInvertible) :
    ‖(cylinderOperator T S).inverse‖ ≤ √(1 + ‖(loopOperator T S).inverse‖ ^ 2) := by
  simpa only [cylinderOperator, norm_inverse_I_smul_loopOperator] using
    WeakDerivStep.norm_inverse_domainTrajectoryOperator_le
      (ι := cylinderInclusion)
      (real_inner_I_smul_loopOperator_comm T S hS)
      ((isInvertible_I_smul_loopOperator_iff T S).2 hL)

/-- **Spectral-gap `L²` bound on the cylinder.** If `S` is infinitesimally symplectic and
`c ‖ι a‖ ≤ ‖loopOperator T S a‖` for all `a ∈ H¹` (`c > 0`), then
`‖ι ∘ u‖_{L²} ≤ c⁻¹ ‖cylinderOperator T S u‖_{L²}`. -/
theorem norm_compLpL_cylinderInclusion_le_inv_mul_norm_cylinderOperator
    {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    {c : ℝ} (hc : 0 < c)
    (hgap : ∀ a : CircleSobolev 1 F, c * ‖inclusion zero_le_one a‖ ≤ ‖loopOperator T S a‖)
    (u : WeakDerivStep volume ⊤ 2
      (cylinderInclusion (E := F).compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    ‖cylinderInclusion.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
        (WeakDerivStep.prev
          (cylinderInclusion.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u)‖ ≤
      c⁻¹ * ‖cylinderOperator T S u‖ := by
  refine WeakDerivStep.norm_compLpL_le_inv_mul_norm_domainTrajectoryOperator
    (real_inner_I_smul_loopOperator_comm T S hS) hc (fun a ↦ ?_) u
  rw [smul_apply, norm_smul, norm_I, one_mul, cylinderInclusion_apply]
  exact hgap a

/-- **Uniform weighted cylinder inverses from loop nondegeneracy.** Over a compact parameter set
`K` of infinitesimally symplectic nondegenerate loops `S p` and any continuous perturbation family
`J p` (in particular `J p = const (I • id)` for exponential weights), `cylinderOperator T (S p -
δ • J p)` is invertible with uniformly bounded inverse for all `|δ| ≤ ε`. -/
theorem exists_pos_isInvertible_cylinderOperator_sub_smul_of_isInvertible_loopOperator
    {P : Type*} [TopologicalSpace P] {K : Set P} (hK : IsCompact K)
    (S J : P → C(AddCircle T, F →L[ℝ] F)) (hS : ContinuousOn S K) (hJ : ContinuousOn J K)
    (hSymm : ∀ p ∈ K, ∀ t v w, (inner ℂ (S p t v) w).im + (inner ℂ v (S p t w)).im = 0)
    (hinv : ∀ p ∈ K, (loopOperator T (S p)).IsInvertible) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ p ∈ K, ∀ δ : ℝ, |δ| ≤ ε →
      (cylinderOperator T (S p - δ • J p)).IsInvertible ∧
        ‖(cylinderOperator T (S p - δ • J p)).inverse‖ ≤ C :=
  exists_pos_isInvertible_cylinderOperator_sub_smul_norm_inverse_le T hK S J hS hJ fun p hp ↦
    (isInvertible_cylinderOperator_iff_isInvertible_loopOperator T (hSymm p hp)).2 (hinv p hp)

/-- **Eigenmode injection on the cylinder.** Along an eigenvector `I • loopOperator T S a = λ • ι a`
and a scalar profile `w ∈ W^{1,2}(ℝ)`, `cylinderOperator T S` acts as
`s ↦ (w' s + λ w s) • ι a`. -/
theorem cylinderOperator_smulRightBaseW1pL_of_eigenvector_ae {S : C(AddCircle T, F →L[ℝ] F)}
    {a : CircleSobolev 1 F} {lam : ℝ}
    (ha : I • loopOperator T S a = lam • inclusion zero_le_one a)
    (w : W1p volume ⊤ 2) :
    cylinderOperator T S (WeakDerivStep.smulRightBaseW1pL cylinderInclusion a w)
      =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (⟪W1p.gradient w s, (1 : ℝ)⟫_ℝ + lam * W1p.value w s) •
        inclusion zero_le_one a := by
  filter_upwards [WeakDerivStep.domainTrajectoryOperator_smulRightBaseW1pL_ae
      cylinderInclusion (I • loopOperator T S) a w] with s hs
  rw [cylinderOperator, hs, smul_apply, ha, cylinderInclusion_apply, smul_smul, mul_comm, add_smul]

/-- **Eigenmode projection on the cylinder.** For an infinitesimally symplectic loop `S` and an
eigenvector `I • loopOperator T S a = λ • ι a`, projecting `cylinderOperator T S u` against `ι a`
yields the scalar `W^{1,2}(ℝ)` differential expression `u_a' + λ u_a`. -/
theorem compLpL_innerSL_cylinderOperator_of_eigenvector_ae {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    {a : CircleSobolev 1 F} {lam : ℝ}
    (ha : I • loopOperator T S a = lam • inclusion zero_le_one a)
    (u : WeakDerivStep volume ⊤ 2
      (cylinderInclusion (E := F).compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    (innerSL ℝ (inclusion zero_le_one a)).compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
        (cylinderOperator T S u)
      =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ ⟪W1p.gradient (WeakDerivStep.toW1pL
            (cylinderInclusion.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
            (innerSL ℝ (inclusion zero_le_one a)) u) s, (1 : ℝ)⟫_ℝ +
        lam * W1p.value (WeakDerivStep.toW1pL
            (cylinderInclusion.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
            (innerSL ℝ (inclusion zero_le_one a)) u) s := by
  refine WeakDerivStep.compLpL_innerSL_domainTrajectoryOperator_ae
    cylinderInclusion (I • loopOperator T S) (inclusion zero_le_one a) (fun x ↦ ?_) u
  rw [smul_apply, ← real_inner_I_smul_loopOperator_comm T S hS a x, ha,
    inner_smul_left, RCLike.conj_to_real, cylinderInclusion_apply]

end Symplectic

end TauCeti.CircleSobolev
