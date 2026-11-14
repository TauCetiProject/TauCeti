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
real-linear Sobolev inclusion `ι = (CircleSobolev.inclusion zero_le_one).restrictScalars ℝ` from
`H¹(AddCircle T, E)` to `H⁰(AddCircle T, E)` defines the common-domain Sobolev graph space

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
  3. `cylinderOperator T S` has closed range;
  4. `loopOperator T S` is invertible;
  5. `ζ' = S ζ` admits no nonzero continuous `T`-periodic solution `ζ`.
* **Pythagorean identity and inverse bound.** For every infinitesimally symplectic loop `S`,
  `‖cylinderOperator T S u‖² = ‖(ι ∘ u)'‖² + ‖(I • L_S) ∘ u‖²`, and at a nondegenerate loop
  `‖(cylinderOperator T S).inverse‖ ≤ √(1 + ‖(loopOperator T S).inverse‖²)`.
* **Exponential weight shifts and compact-family uniformity.** Subtracting the constant loop
  `δ • (I • id)` from `S` subtracts `δ • ι ∘ prev` from `cylinderOperator T S`, realizing the
  conjugated operator `e^{δ s} (∂s + A) e^{-δ s}` on exponentially weighted ends. Over any compact
  parameter set `K` on which both the loop family `S` and perturbation family `J` are continuous and
  each `S p` is nondegenerate, all sufficiently small weights `|δ| ≤ ε` remain invertible on the
  cylinder with a uniform operator-norm bound on the inverse (adapting
  `TauCeti.CircleSobolev.exists_pos_isInvertible_loopOperator_sub_smul_norm_inverse_le` in
  `TauCeti/Analysis/Sobolev/Circle/LinearODE/Family.lean` via
  `IsCompact.exists_pos_isInvertible_map_sub_smul_norm_inverse_le`).
* **Eigenmode splitting.** Along any solution of `I • loopOperator T S a = λ • ι a` (such as the
  Hilbert eigenbasis of `TauCeti.CircleSobolev.exists_hilbertBasis_I_smul_loopOperator_eq_smul`),
  scalar mode injection and projection intertwine `cylinderOperator T S` with the scalar
  differential expression `w' + λ w`.

## Main declarations

* `TauCeti.CircleSobolev.cylinderOperator`, `TauCeti.CircleSobolev.cylinderOperator_def`:
  the stationary cylinder operator `∂s ∘ ι + I • L_S` and its unfolding to
  `WeakDerivStep.domainTrajectoryOperator`.
* `TauCeti.CircleSobolev.cylinderOperator_sub`,
  `TauCeti.CircleSobolev.cylinderOperator_sub_smul_const_I`: zero-order loop differences and
  exponential weight shifts `S - δ I` on the cylinder.
* `TauCeti.CircleSobolev.norm_cylinderOperator_sq`,
  `TauCeti.CircleSobolev.injective_cylinderOperator`: Pythagorean squared-norm identity and
  unconditional injectivity for infinitesimally symplectic loops.
* `TauCeti.CircleSobolev.isClosed_range_cylinderOperator_iff_isInvertible_loopOperator`,
  `TauCeti.CircleSobolev.isFredholm_cylinderOperator_iff_isInvertible_loopOperator`,
  `TauCeti.CircleSobolev.isInvertible_cylinderOperator_iff_isInvertible_loopOperator`,
  `TauCeti.CircleSobolev.isInvertible_cylinderOperator_iff`: equivalences between closed range,
  Fredholmness, and invertibility on the cylinder, loop invertibility, and absence of periodic
  solutions.
* `TauCeti.CircleSobolev.norm_inverse_cylinderOperator_le`,
  `TauCeti.CircleSobolev.norm_compLpL_inclusion_le_inv_mul_norm_cylinderOperator`: inverse norm
  bound `√(1 + ‖(loopOperator T S).inverse‖²)` and spectral-gap `L²` bound.
* `TauCeti.CircleSobolev.exists_pos_isInvertible_cylinderOperator_sub_smul_norm_inverse_le` and
  `exists_pos_isInvertible_cylinderOperator_sub_smul_norm_inverse_le_of_isInvertible_loopOperator`:
  uniform weighted cylinder inverses over compact families.
* `TauCeti.CircleSobolev.cylinderOperator_smulRightBaseW1pL_ae_of_I_smul_loopOperator_eq_smul` and
  `TauCeti.CircleSobolev.compLpL_innerSL_cylinderOperator_ae_of_I_smul_loopOperator_eq_smul`:
  scalar eigenmode injection and projection on the cylinder.

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

/-! ### The stationary cylinder operator on a complex normed space -/

section Normed

variable (T : ℝ) [Fact (0 < T)] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]

local instance : CompleteSpace E := FiniteDimensional.completeSpace ℂ E

/-- **The stationary cylinder operator** `∂s ∘ ι + I • L_S` from
`L²(ℝ, H¹(AddCircle T, E)) ∩ W^{1,2}(ℝ, H⁰(AddCircle T, E))` to `L²(ℝ, H⁰(AddCircle T, E))`. -/
def cylinderOperator (S : C(AddCircle T, E →L[ℝ] E)) :
    WeakDerivStep volume ⊤ 2
      (((inclusion (E := E) zero_le_one).restrictScalars ℝ).compLpL 2
        (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) →L[ℝ]
    Lp (CircleSobolev 0 E) 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
  WeakDerivStep.domainTrajectoryOperator
    ((inclusion (E := E) zero_le_one).restrictScalars ℝ) (I • loopOperator T S)

/-- Unfolding formula for `cylinderOperator` in terms of
`WeakDerivStep.domainTrajectoryOperator`. -/
theorem cylinderOperator_def (S : C(AddCircle T, E →L[ℝ] E)) :
    cylinderOperator T S =
      WeakDerivStep.domainTrajectoryOperator
        ((inclusion (E := E) zero_le_one).restrictScalars ℝ) (I • loopOperator T S) :=
  (rfl)

/-- Explicit `L²` decomposition of `cylinderOperator T S u` into its `s`-derivative and slice
components. -/
theorem cylinderOperator_apply (S : C(AddCircle T, E →L[ℝ] E))
    (u : WeakDerivStep volume ⊤ 2
      (((inclusion (E := E) zero_le_one).restrictScalars ℝ).compLpL 2
        (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    cylinderOperator T S u =
      (ContinuousLinearMap.apply ℝ (CircleSobolev 0 E) (1 : ℝ)).compLpL 2
        (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
        (WeakDerivStep.weakFDeriv
          (((inclusion (E := E) zero_le_one).restrictScalars ℝ).compLpL 2
            (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u) +
      (I • loopOperator T S).compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
        (WeakDerivStep.prev
          (((inclusion (E := E) zero_le_one).restrictScalars ℝ).compLpL 2
            (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u) :=
  WeakDerivStep.domainTrajectoryOperator_apply _ _ u

/-- `cylinderOperator T` depends continuously in operator norm on the coefficient loop `S`. -/
@[fun_prop]
theorem continuous_cylinderOperator : Continuous (cylinderOperator (E := E) T) :=
  (WeakDerivStep.continuous_domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2)
    ((inclusion (E := E) zero_le_one).restrictScalars ℝ)).comp
    ((continuous_loopOperator T).const_smul I)

/-- Subtracting `S₂` from the coefficient loop adds `(I • mulLoop T _ S₂) ∘ prev` to
`cylinderOperator T S₁`. -/
theorem cylinderOperator_sub (S₁ S₂ : C(AddCircle T, E →L[ℝ] E)) :
    cylinderOperator T (S₁ - S₂) =
      cylinderOperator T S₁ +
        ((I • mulLoop T (by norm_num) S₂).compLpL 2
          (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))).comp
          (WeakDerivStep.prevL
            (((inclusion (E := E) zero_le_one).restrictScalars ℝ).compLpL 2
              (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) := by
  have hsub := WeakDerivStep.domainTrajectoryOperator_sub (mu := volume) (Omega := ⊤) (p := 2)
    ((inclusion (E := E) zero_le_one).restrictScalars ℝ)
    (I • loopOperator T (S₁ - S₂)) (I • loopOperator T S₁)
  have hdiff : I • loopOperator T (S₁ - S₂) - I • loopOperator T S₁ =
      I • mulLoop T (by norm_num) S₂ := by
    rw [loopOperator_sub, smul_add, add_sub_cancel_left]
  rw [← cylinderOperator_def, ← cylinderOperator_def, hdiff] at hsub
  exact sub_eq_iff_eq_add'.mp hsub

/-- **Weighted cylinder shift.** Replacing `S` by `S - δ • const (I • id)` subtracts
`δ • (ι ∘ prev)` from `cylinderOperator T S`, matching conjugation of `∂s + A` by `e^{δ s}`. -/
theorem cylinderOperator_sub_smul_const_I (S : C(AddCircle T, E →L[ℝ] E)) (δ : ℝ) :
    cylinderOperator T (S - δ • ContinuousMap.const _ (I • ContinuousLinearMap.id ℝ E)) =
      cylinderOperator T S -
        δ • ((((inclusion (E := E) zero_le_one).restrictScalars ℝ).compLpL 2
          (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))).comp
          (WeakDerivStep.prevL
            (((inclusion (E := E) zero_le_one).restrictScalars ℝ).compLpL 2
              (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) := by
  rw [cylinderOperator_sub, sub_eq_add_neg]
  ext u : 1
  simp only [add_apply, neg_apply, smul_apply, ContinuousLinearMap.comp_apply]
  congr 1
  have hloop :
      I • mulLoop T (by norm_num) (δ • ContinuousMap.const _ (I • ContinuousLinearMap.id ℝ E)) =
        (-δ) • (inclusion (E := E) zero_le_one).restrictScalars ℝ := by
    have h := I_smul_loopOperator_sub_smul_const_I T S δ
    rw [loopOperator_sub, smul_add, sub_eq_add_neg, ← neg_smul] at h
    exact add_left_cancel h
  refine (congrArg (fun L ↦ L.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
    (WeakDerivStep.prevL _ u)) hloop).trans ?_
  have hs := congrArg (· (WeakDerivStep.prevL _ u))
    (ContinuousLinearMap.smul_compLpL (p := 2)
      (μ := volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) (-δ)
      ((inclusion (E := E) zero_le_one).restrictScalars ℝ))
  exact hs.trans (by rw [smul_apply, neg_smul])

/-- **Uniform weighted cylinder inverses over a compact family.** If `S` and `J` are continuous on a
compact parameter set `K` and `cylinderOperator T (S p)` is invertible for every `p ∈ K`, then there
are `ε > 0` and `C ≥ 0` such that `cylinderOperator T (S p - δ • J p)` is invertible with inverse
norm at most `C` for all `p ∈ K` and `|δ| ≤ ε`. -/
theorem exists_pos_isInvertible_cylinderOperator_sub_smul_norm_inverse_le
    {P : Type*} [TopologicalSpace P] {K : Set P} (hK : IsCompact K)
    (S J : P → C(AddCircle T, E →L[ℝ] E)) (hS : ContinuousOn S K) (hJ : ContinuousOn J K)
    (hinv : ∀ p ∈ K, (cylinderOperator T (S p)).IsInvertible) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ p ∈ K, ∀ δ : ℝ, |δ| ≤ ε →
      (cylinderOperator T (S p - δ • J p)).IsInvertible ∧
        ‖(cylinderOperator T (S p - δ • J p)).inverse‖ ≤ C :=
  hK.exists_pos_isInvertible_map_sub_smul_norm_inverse_le
    (continuous_cylinderOperator T) S J hS hJ hinv

/-- **Eigenmode injection on the cylinder.** Along a solution `a` of
`I • loopOperator T S a = λ • ι a` and a scalar profile `w ∈ W^{1,2}(ℝ)`, `cylinderOperator T S`
acts as `s ↦ (w' s + λ w s) • ι a`. -/
theorem cylinderOperator_smulRightBaseW1pL_ae_of_I_smul_loopOperator_eq_smul
    {S : C(AddCircle T, E →L[ℝ] E)} {a : CircleSobolev 1 E} {lam : ℝ}
    (ha : I • loopOperator T S a = lam • inclusion zero_le_one a) (w : W1p volume ⊤ 2) :
    cylinderOperator T S
        (WeakDerivStep.smulRightBaseW1pL ((inclusion (E := E) zero_le_one).restrictScalars ℝ) a w)
      =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (⟪W1p.gradient w s, (1 : ℝ)⟫_ℝ + lam * W1p.value w s) •
        inclusion zero_le_one a := by
  filter_upwards [WeakDerivStep.domainTrajectoryOperator_smulRightBaseW1pL_ae
      ((inclusion (E := E) zero_le_one).restrictScalars ℝ) (I • loopOperator T S) a w] with s hs
  rw [cylinderOperator, hs, smul_apply, ha,
    ContinuousLinearMap.coe_restrictScalars', smul_smul, mul_comm, add_smul]

end Normed

/-! ### Infinitesimally symplectic loops: symmetry, invertibility, and eigenmode projection -/

section Symplectic

variable (T : ℝ) [Fact (0 < T)] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

local instance : CompleteSpace F := FiniteDimensional.completeSpace ℂ F

/-- **Pythagorean identity on the cylinder.** For an infinitesimally symplectic loop `S`,
`‖cylinderOperator T S u‖² = ‖(ι ∘ u)'‖² + ‖(I • L_S) ∘ u‖²` on `L²(ℝ, H¹) ∩ W^{1,2}(ℝ, H⁰)`. -/
theorem norm_cylinderOperator_sq {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (u : WeakDerivStep volume ⊤ 2
      (((inclusion (E := F) zero_le_one).restrictScalars ℝ).compLpL 2
        (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    ‖cylinderOperator T S u‖ ^ 2 =
      ‖WeakDerivStep.weakFDeriv
          (((inclusion (E := F) zero_le_one).restrictScalars ℝ).compLpL 2
            (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u‖ ^ 2 +
        ‖(I • loopOperator T S).compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
          (WeakDerivStep.prev
            (((inclusion (E := F) zero_le_one).restrictScalars ℝ).compLpL 2
              (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u)‖ ^ 2 :=
  WeakDerivStep.norm_domainTrajectoryOperator_sq
    (real_inner_I_smul_loopOperator_comm T S hS) u

/-- **Injectivity on the cylinder.** For any infinitesimally symplectic loop `S` (even a degenerate
one), `cylinderOperator T S` has trivial kernel on `L²(ℝ, H¹) ∩ W^{1,2}(ℝ, H⁰)`. -/
theorem injective_cylinderOperator {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    Function.Injective (cylinderOperator T S) :=
  WeakDerivStep.injective_domainTrajectoryOperator_of_symmetric
    (inclusion_injective zero_le_one) (real_inner_I_smul_loopOperator_comm T S hS)

/-- **Closed-range equivalence: cylinder vs. loop.** For an infinitesimally symplectic loop `S`, the
range of `cylinderOperator T S` is closed if and only if `loopOperator T S` is invertible. -/
theorem isClosed_range_cylinderOperator_iff_isInvertible_loopOperator
    {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    IsClosed ((cylinderOperator T S).range :
      Set (Lp (CircleSobolev 0 F) 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ↔
      (loopOperator T S).IsInvertible := by
  rw [cylinderOperator, WeakDerivStep.isClosed_range_domainTrajectoryOperator_iff
    (inclusion_injective zero_le_one) (real_inner_I_smul_loopOperator_comm T S hS)
    (isFredholm_I_smul_loopOperator T S) (index_I_smul_loopOperator T S),
    isInvertible_I_smul_loopOperator_iff]

/-- **Invertibility equivalence: cylinder vs. loop.** For an infinitesimally symplectic loop `S`,
the stationary cylinder operator `∂s ∘ ι + I • L_S` is invertible if and only if the periodic loop
operator `L_S` is invertible. -/
theorem isInvertible_cylinderOperator_iff_isInvertible_loopOperator
    {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (cylinderOperator T S).IsInvertible ↔ (loopOperator T S).IsInvertible := by
  rw [cylinderOperator, WeakDerivStep.isInvertible_domainTrajectoryOperator_iff
    (inclusion_injective zero_le_one) (real_inner_I_smul_loopOperator_comm T S hS)
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
    (inclusion_injective zero_le_one) (real_inner_I_smul_loopOperator_comm T S hS)
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
      (ι := (inclusion (E := F) zero_le_one).restrictScalars ℝ)
      (real_inner_I_smul_loopOperator_comm T S hS)
      ((isInvertible_I_smul_loopOperator_iff T S).2 hL)

/-- **Spectral-gap `L²` bound on the cylinder.** If `S` is infinitesimally symplectic and
`c ‖ι a‖ ≤ ‖loopOperator T S a‖` for all `a ∈ H¹` (`c > 0`), then
`‖ι ∘ u‖_{L²} ≤ c⁻¹ ‖cylinderOperator T S u‖_{L²}`. -/
theorem norm_compLpL_inclusion_le_inv_mul_norm_cylinderOperator
    {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    {c : ℝ} (hc : 0 < c)
    (hgap : ∀ a : CircleSobolev 1 F, c * ‖inclusion zero_le_one a‖ ≤ ‖loopOperator T S a‖)
    (u : WeakDerivStep volume ⊤ 2
      (((inclusion (E := F) zero_le_one).restrictScalars ℝ).compLpL 2
        (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    ‖((inclusion (E := F) zero_le_one).restrictScalars ℝ).compLpL 2
        (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
        (WeakDerivStep.prev
          (((inclusion (E := F) zero_le_one).restrictScalars ℝ).compLpL 2
            (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u)‖ ≤
      c⁻¹ * ‖cylinderOperator T S u‖ := by
  refine WeakDerivStep.norm_compLpL_le_inv_mul_norm_domainTrajectoryOperator
    (real_inner_I_smul_loopOperator_comm T S hS) hc (fun a ↦ ?_) u
  rw [smul_apply, norm_smul, norm_I, one_mul,
    ContinuousLinearMap.coe_restrictScalars']
  exact hgap a

/-- **Uniform weighted cylinder inverses from loop nondegeneracy.** Over a compact parameter set
`K` on which both the infinitesimally symplectic nondegenerate loop family `S` and perturbation
family `J` (in particular `J p = const (I • id)` for exponential weights) are continuous, there are
`ε > 0` and `C ≥ 0` such that `cylinderOperator T (S p - δ • J p)` is invertible with inverse norm
at most `C` for all `p ∈ K` and `|δ| ≤ ε`. -/
theorem
    exists_pos_isInvertible_cylinderOperator_sub_smul_norm_inverse_le_of_isInvertible_loopOperator
    {P : Type*} [TopologicalSpace P] {K : Set P} (hK : IsCompact K)
    (S J : P → C(AddCircle T, F →L[ℝ] F)) (hS : ContinuousOn S K) (hJ : ContinuousOn J K)
    (hSymm : ∀ p ∈ K, ∀ t v w, (inner ℂ (S p t v) w).im + (inner ℂ v (S p t w)).im = 0)
    (hinv : ∀ p ∈ K, (loopOperator T (S p)).IsInvertible) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ p ∈ K, ∀ δ : ℝ, |δ| ≤ ε →
      (cylinderOperator T (S p - δ • J p)).IsInvertible ∧
        ‖(cylinderOperator T (S p - δ • J p)).inverse‖ ≤ C :=
  exists_pos_isInvertible_cylinderOperator_sub_smul_norm_inverse_le T hK S J hS hJ fun p hp ↦
    (isInvertible_cylinderOperator_iff_isInvertible_loopOperator T (hSymm p hp)).2 (hinv p hp)

/-- **Eigenmode projection on the cylinder.** For an infinitesimally symplectic loop `S` and a
solution `a` of `I • loopOperator T S a = λ • ι a`, projecting `cylinderOperator T S u` against
`ι a` yields the scalar `W^{1,2}(ℝ)` differential expression `u_a' + λ u_a`. -/
theorem compLpL_innerSL_cylinderOperator_ae_of_I_smul_loopOperator_eq_smul
    {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    {a : CircleSobolev 1 F} {lam : ℝ}
    (ha : I • loopOperator T S a = lam • inclusion zero_le_one a)
    (u : WeakDerivStep volume ⊤ 2
      (((inclusion (E := F) zero_le_one).restrictScalars ℝ).compLpL 2
        (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    (innerSL ℝ (inclusion zero_le_one a)).compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
        (cylinderOperator T S u)
      =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ ⟪W1p.gradient (WeakDerivStep.toW1pL
            (((inclusion (E := F) zero_le_one).restrictScalars ℝ).compLpL 2
              (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
            (innerSL ℝ (inclusion zero_le_one a)) u) s, (1 : ℝ)⟫_ℝ +
        lam * W1p.value (WeakDerivStep.toW1pL
            (((inclusion (E := F) zero_le_one).restrictScalars ℝ).compLpL 2
              (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
            (innerSL ℝ (inclusion zero_le_one a)) u) s := by
  refine WeakDerivStep.compLpL_domainTrajectoryOperator_ae
    ((inclusion (E := F) zero_le_one).restrictScalars ℝ) (I • loopOperator T S)
    (innerSL ℝ (inclusion zero_le_one a)) (fun x ↦ ?_) u
  rw [innerSL_apply_apply, smul_apply,
    ← real_inner_I_smul_loopOperator_comm T S hS a x, ha,
    inner_smul_left, RCLike.conj_to_real, innerSL_apply_apply,
    ContinuousLinearMap.coe_restrictScalars']

end Symplectic

end TauCeti.CircleSobolev
