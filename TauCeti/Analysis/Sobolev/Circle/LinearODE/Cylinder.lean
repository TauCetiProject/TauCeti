/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain
public import TauCeti.Analysis.Sobolev.Circle.LinearODE.Eigenbasis
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.Normed.Operator.CompactFamily
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# The stationary cylinder operator over periodic circle Sobolev spaces

In a unitary frame on a finite-dimensional complex space `E`, the linearized Cauchy–Riemann /
stationary Hamiltonian Floer operator on `ℝ × AddCircle T` (`T > 0`) takes the autonomous form
`∂s + I (∂t - S_t)` for `S : C(AddCircle T, E →L[ℝ] E)`. Feeding
`ι = (CircleSobolev.inclusion zero_le_one).restrictScalars ℝ` and `I • loopOperator T S` into
`TauCeti.WeakDerivStep.domainTrajectoryOperator` gives its `W^{1,2}` realization
`TauCeti.CircleSobolev.cylinderOperator T S` on
`L²(ℝ, H¹(AddCircle T, E)) ∩ W^{1,2}(ℝ, H⁰(AddCircle T, E))`; perturbations `S - δ • J` encode
exponential weight shifts `e^{±δ s}` on cylindrical ends, feeding
`TauCeti/Geometry/Symplectic/Floer/AsymptoticOperator/Cylinder.lean`.

When `F` is a finite-dimensional complex inner product space and `S` is infinitesimally symplectic
(`Im ⟪S t v, w⟫ + Im ⟪v, S t w⟫ = 0`), `I • loopOperator T S` is `ι`-symmetric and index-`0`
Fredholm, yielding unconditional injectivity, equivalence of closed range / Fredholmness /
invertibility (for either sign `∂s ± I • loopOperator T S`) with `loopOperator T S` invertibility
— equivalently nondegeneracy of the periodic orbit — the Pythagorean identity and improved inverse
bound `max ‖(loopOperator T S)⁻¹‖ 1`, uniform weighted inverses over compact families (adapting
`TauCeti/Analysis/Sobolev/Circle/LinearODE/Family.lean`), and eigenmode intertwining (`w' + λ w`).

## References

* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. **7** (1999), Lecture 2,
  Proposition 2.2.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33, Theorem 4.17.
-/

public section

noncomputable section

open Complex Filter _root_.MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology

namespace TauCeti.CircleSobolev

local notation "μ₀" => (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))

section Normed

variable (T : ℝ) [Fact (0 < T)] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]

local instance : CompleteSpace E := FiniteDimensional.completeSpace ℂ E

/-- The stationary cylinder operator `∂s ∘ ι + I • L_S` from
`L²(ℝ, H¹(AddCircle T, E)) ∩ W^{1,2}(ℝ, H⁰(AddCircle T, E))` to `L²(ℝ, H⁰(AddCircle T, E))`. -/
def cylinderOperator (S : C(AddCircle T, E →L[ℝ] E)) :
    WeakDerivStep volume ⊤ 2
      (((inclusion (E := E) zero_le_one).restrictScalars ℝ).compLpL 2 μ₀) →L[ℝ]
      Lp (CircleSobolev 0 E) 2 μ₀ :=
  WeakDerivStep.domainTrajectoryOperator
    ((inclusion (E := E) zero_le_one).restrictScalars ℝ) (I • loopOperator T S)

/-- Unfolding formula for `cylinderOperator` via `WeakDerivStep.domainTrajectoryOperator`. -/
theorem cylinderOperator_def (S : C(AddCircle T, E →L[ℝ] E)) :
    cylinderOperator T S = WeakDerivStep.domainTrajectoryOperator
      ((inclusion (E := E) zero_le_one).restrictScalars ℝ) (I • loopOperator T S) := (rfl)

/-- Explicit `L²` decomposition of `cylinderOperator T S u` into `s`-derivative and slice parts. -/
theorem cylinderOperator_apply (S : C(AddCircle T, E →L[ℝ] E))
    (u : WeakDerivStep volume ⊤ 2
      (((inclusion (E := E) zero_le_one).restrictScalars ℝ).compLpL 2 μ₀)) :
    cylinderOperator T S u =
      (ContinuousLinearMap.apply ℝ (CircleSobolev 0 E) (1 : ℝ)).compLpL 2 μ₀
        (WeakDerivStep.weakFDeriv
          (((inclusion (E := E) zero_le_one).restrictScalars ℝ).compLpL 2 μ₀) u) +
      (I • loopOperator T S).compLpL 2 μ₀ (WeakDerivStep.prev
        (((inclusion (E := E) zero_le_one).restrictScalars ℝ).compLpL 2 μ₀) u) :=
  WeakDerivStep.domainTrajectoryOperator_apply _ _ u

/-- `cylinderOperator T` depends continuously in operator norm on `S`. -/
@[fun_prop] theorem continuous_cylinderOperator : Continuous (cylinderOperator (E := E) T) :=
  (WeakDerivStep.continuous_domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2)
    ((inclusion (E := E) zero_le_one).restrictScalars ℝ)).comp
    ((continuous_loopOperator T).const_smul I)

/-- Subtracting `S₂` from the loop adds `(I • mulLoop T _ S₂) ∘ prev` to `cylinderOperator T S₁`. -/
theorem cylinderOperator_sub (S₁ S₂ : C(AddCircle T, E →L[ℝ] E)) :
    cylinderOperator T (S₁ - S₂) = cylinderOperator T S₁ +
      ((I • mulLoop T (by norm_num) S₂).compLpL 2 μ₀).comp (WeakDerivStep.prevL
        (((inclusion (E := E) zero_le_one).restrictScalars ℝ).compLpL 2 μ₀)) := by
  have hsub := WeakDerivStep.domainTrajectoryOperator_sub (mu := volume) (Omega := ⊤) (p := 2)
    ((inclusion (E := E) zero_le_one).restrictScalars ℝ)
    (I • loopOperator T (S₁ - S₂)) (I • loopOperator T S₁)
  have hdiff : I • loopOperator T (S₁ - S₂) - I • loopOperator T S₁ =
      I • mulLoop T (by norm_num) S₂ := by rw [loopOperator_sub, smul_add, add_sub_cancel_left]
  rw [← cylinderOperator_def, ← cylinderOperator_def, hdiff] at hsub
  exact sub_eq_iff_eq_add'.mp hsub

/-- Replacing `S` by `S - δ • const (I • id)` subtracts `δ • (ι ∘ prev)` from
`cylinderOperator T S`. -/
theorem cylinderOperator_sub_smul_const_I (S : C(AddCircle T, E →L[ℝ] E)) (δ : ℝ) :
    cylinderOperator T (S - δ • ContinuousMap.const _ (I • ContinuousLinearMap.id ℝ E)) =
      cylinderOperator T S -
        δ • ((((inclusion (E := E) zero_le_one).restrictScalars ℝ).compLpL 2 μ₀).comp
          (WeakDerivStep.prevL
            (((inclusion (E := E) zero_le_one).restrictScalars ℝ).compLpL 2 μ₀))) := by
  rw [cylinderOperator_sub, sub_eq_add_neg]; ext u : 1
  simp only [add_apply, neg_apply, smul_apply, ContinuousLinearMap.comp_apply]; congr 1
  have hloop :
      I • mulLoop T (by norm_num) (δ • ContinuousMap.const _ (I • ContinuousLinearMap.id ℝ E)) =
        (-δ) • (inclusion (E := E) zero_le_one).restrictScalars ℝ := by
    have h := I_smul_loopOperator_sub_smul_const_I T S δ
    rw [loopOperator_sub, smul_add, sub_eq_add_neg, ← neg_smul] at h
    exact add_left_cancel h
  refine (congrArg (fun L ↦ L.compLpL 2 μ₀ (WeakDerivStep.prevL _ u)) hloop).trans ?_
  exact (congrArg (· (WeakDerivStep.prevL _ u))
    (ContinuousLinearMap.smul_compLpL (p := 2) (μ := μ₀) (-δ)
      ((inclusion (E := E) zero_le_one).restrictScalars ℝ))).trans (by rw [smul_apply, neg_smul])

/-- If `S` and `J` are continuous on compact `K` and each `cylinderOperator T (S p)` is invertible,
`cylinderOperator T (S p - δ • J p)` has inverse norm at most `C` for `p ∈ K` and `|δ| ≤ ε`. -/
theorem exists_pos_isInvertible_cylinderOperator_sub_smul_norm_inverse_le
    {P : Type*} [TopologicalSpace P] {K : Set P} (hK : IsCompact K)
    (S J : P → C(AddCircle T, E →L[ℝ] E)) (hS : ContinuousOn S K) (hJ : ContinuousOn J K)
    (hinv : ∀ p ∈ K, (cylinderOperator T (S p)).IsInvertible) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ p ∈ K, ∀ δ : ℝ, |δ| ≤ ε →
      (cylinderOperator T (S p - δ • J p)).IsInvertible ∧
        ‖(cylinderOperator T (S p - δ • J p)).inverse‖ ≤ C :=
  hK.exists_pos_isInvertible_map_sub_smul_norm_inverse_le
    (continuous_cylinderOperator T) S J hS hJ hinv

/-- Eigenmode injection on the cylinder along `I • loopOperator T S a = λ • ι a`. -/
theorem cylinderOperator_smulRightBaseW1pL_ae_of_I_smul_loopOperator_eq_smul
    {S : C(AddCircle T, E →L[ℝ] E)} {a : CircleSobolev 1 E} {lam : ℝ}
    (ha : I • loopOperator T S a = lam • inclusion zero_le_one a) (w : W1p volume ⊤ 2) :
    cylinderOperator T S
        (WeakDerivStep.smulRightBaseW1pL ((inclusion (E := E) zero_le_one).restrictScalars ℝ) a w)
      =ᵐ[μ₀] fun s ↦ (⟪W1p.gradient w s, (1 : ℝ)⟫_ℝ + lam * W1p.value w s) •
        inclusion zero_le_one a := by
  filter_upwards [WeakDerivStep.domainTrajectoryOperator_smulRightBaseW1pL_ae
    ((inclusion (E := E) zero_le_one).restrictScalars ℝ) (I • loopOperator T S) a w] with s hs
  rw [cylinderOperator, hs, smul_apply, ha, ContinuousLinearMap.coe_restrictScalars', smul_smul,
    mul_comm, add_smul]

end Normed

section Symplectic

variable (T : ℝ) [Fact (0 < T)] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

local instance : CompleteSpace F := FiniteDimensional.completeSpace ℂ F

/-- Pythagorean identity `‖cylinderOperator T S u‖² = ‖(ι ∘ u)'‖² + ‖(I • L_S) ∘ u‖²` for an
infinitesimally symplectic loop `S`. -/
theorem norm_cylinderOperator_sq {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (u : WeakDerivStep volume ⊤ 2
      (((inclusion (E := F) zero_le_one).restrictScalars ℝ).compLpL 2 μ₀)) :
    ‖cylinderOperator T S u‖ ^ 2 =
      ‖WeakDerivStep.weakFDeriv
          (((inclusion (E := F) zero_le_one).restrictScalars ℝ).compLpL 2 μ₀) u‖ ^ 2 +
        ‖(I • loopOperator T S).compLpL 2 μ₀ (WeakDerivStep.prev
          (((inclusion (E := F) zero_le_one).restrictScalars ℝ).compLpL 2 μ₀) u)‖ ^ 2 :=
  WeakDerivStep.norm_domainTrajectoryOperator_sq (real_inner_I_smul_loopOperator_comm T S hS) u

/-- Injectivity of `cylinderOperator T S` for any infinitesimally symplectic loop `S`. -/
theorem injective_cylinderOperator {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    Function.Injective (cylinderOperator T S) :=
  WeakDerivStep.injective_domainTrajectoryOperator_of_symmetric
    (inclusion_injective zero_le_one) (real_inner_I_smul_loopOperator_comm T S hS)

/-- For infinitesimally symplectic `S`, `(cylinderOperator T S).range` is closed iff
`loopOperator T S` is invertible. -/
theorem isClosed_range_cylinderOperator_iff_isInvertible_loopOperator
    {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    IsClosed ((cylinderOperator T S).range : Set (Lp (CircleSobolev 0 F) 2 μ₀)) ↔
      (loopOperator T S).IsInvertible := by
  rw [cylinderOperator, WeakDerivStep.isClosed_range_domainTrajectoryOperator_iff
    (inclusion_injective zero_le_one) (real_inner_I_smul_loopOperator_comm T S hS)
    (isFredholm_I_smul_loopOperator T S) (index_I_smul_loopOperator T S),
    ContinuousLinearMap.isInvertible_smul_iff I_ne_zero]

/-- For infinitesimally symplectic `S`, `cylinderOperator T S` is invertible iff `loopOperator T S`
is invertible. -/
theorem isInvertible_cylinderOperator_iff_isInvertible_loopOperator {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (cylinderOperator T S).IsInvertible ↔ (loopOperator T S).IsInvertible := by
  rw [cylinderOperator, WeakDerivStep.isInvertible_domainTrajectoryOperator_iff
    (inclusion_injective zero_le_one) (real_inner_I_smul_loopOperator_comm T S hS)
    (isFredholm_I_smul_loopOperator T S) (index_I_smul_loopOperator T S),
    ContinuousLinearMap.isInvertible_smul_iff I_ne_zero]

/-- For infinitesimally symplectic `S`, `cylinderOperator T S` is Fredholm iff `loopOperator T S`
is invertible. -/
theorem isFredholm_cylinderOperator_iff_isInvertible_loopOperator {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (cylinderOperator T S).IsFredholm ↔ (loopOperator T S).IsInvertible := by
  rw [cylinderOperator, WeakDerivStep.isFredholm_domainTrajectoryOperator_iff
    (inclusion_injective zero_le_one) (real_inner_I_smul_loopOperator_comm T S hS)
    (isFredholm_I_smul_loopOperator T S) (index_I_smul_loopOperator T S),
    ContinuousLinearMap.isInvertible_smul_iff I_ne_zero]

/-- For infinitesimally symplectic `S`, `cylinderOperator T S` is invertible iff `ζ' = S ζ` has no
nonzero continuous `T`-periodic solution. -/
theorem isInvertible_cylinderOperator_iff {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (cylinderOperator T S).IsInvertible ↔
      ∀ ζ : C(AddCircle T, F), (∀ x : ℝ, HasDerivAt (fun y : ℝ ↦ ζ y) (S x (ζ x)) x) → ζ = 0 :=
  (isInvertible_cylinderOperator_iff_isInvertible_loopOperator T hS).trans
    (isInvertible_loopOperator_iff T S)

/-- When `S` is infinitesimally symplectic and `loopOperator T S` is invertible, the Fredholm index
of `cylinderOperator T S` is zero. -/
theorem index_cylinderOperator {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hL : (loopOperator T S).IsInvertible) : (cylinderOperator T S).index = 0 :=
  WeakDerivStep.index_domainTrajectoryOperator (real_inner_I_smul_loopOperator_comm T S hS)
    ((ContinuousLinearMap.isInvertible_smul_iff I_ne_zero).2 hL)

/-- Improved inverse norm bound
`‖(cylinderOperator T S).inverse‖ ≤ max ‖(loopOperator T S).inverse‖ 1`
for infinitesimally symplectic nondegenerate `S`. -/
theorem norm_inverse_cylinderOperator_le_max {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hL : (loopOperator T S).IsInvertible) :
    ‖(cylinderOperator T S).inverse‖ ≤ max ‖(loopOperator T S).inverse‖ 1 := by
  simpa only [cylinderOperator, ContinuousLinearMap.norm_inverse_smul, Complex.norm_I, inv_one,
    one_mul] using
    WeakDerivStep.norm_inverse_domainTrajectoryOperator_le_max
      (ι := (inclusion (E := F) zero_le_one).restrictScalars ℝ)
      (real_inner_I_smul_loopOperator_comm T S hS)
      ((ContinuousLinearMap.isInvertible_smul_iff I_ne_zero).2 hL)

/-- Invertibility of the opposite-sign stationary Floer cylinder operator
`∂s ∘ ι + (-I) • loopOperator T S` for infinitesimally symplectic nondegenerate `S`. -/
theorem isInvertible_domainTrajectoryOperator_neg_I_smul_loopOperator
    {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hL : (loopOperator T S).IsInvertible) :
    (WeakDerivStep.domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2)
      ((inclusion (E := F) zero_le_one).restrictScalars ℝ)
      ((-I) • loopOperator T S)).IsInvertible := by
  rw [neg_smul]
  exact WeakDerivStep.isInvertible_domainTrajectoryOperator_neg
    (real_inner_I_smul_loopOperator_comm T S hS)
    ((ContinuousLinearMap.isInvertible_smul_iff I_ne_zero).2 hL)

/-- If `S` is infinitesimally symplectic and `c ‖ι a‖ ≤ ‖loopOperator T S a‖` (`c > 0`), then
`‖ι ∘ u‖_{L²} ≤ c⁻¹ ‖cylinderOperator T S u‖_{L²}`. -/
theorem norm_compLpL_inclusion_le_inv_mul_norm_cylinderOperator {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ a : CircleSobolev 1 F, c * ‖inclusion zero_le_one a‖ ≤ ‖loopOperator T S a‖)
    (u : WeakDerivStep volume ⊤ 2
      (((inclusion (E := F) zero_le_one).restrictScalars ℝ).compLpL 2 μ₀)) :
    ‖((inclusion (E := F) zero_le_one).restrictScalars ℝ).compLpL 2 μ₀ (WeakDerivStep.prev
      (((inclusion (E := F) zero_le_one).restrictScalars ℝ).compLpL 2 μ₀) u)‖ ≤
      c⁻¹ * ‖cylinderOperator T S u‖ := by
  refine WeakDerivStep.norm_compLpL_le_inv_mul_norm_domainTrajectoryOperator
    (real_inner_I_smul_loopOperator_comm T S hS) hc (fun a ↦ ?_) u
  rw [smul_apply, norm_smul, norm_I, one_mul, ContinuousLinearMap.coe_restrictScalars']
  exact hgap a

/-- Over compact `K` where `S, J` are continuous and each `S p` is infinitesimally symplectic with
invertible `loopOperator`, `cylinderOperator T (S p - δ • J p)` has uniformly bounded inverse for
`p ∈ K` and `|δ| ≤ ε`. -/
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

/-- For infinitesimally symplectic `S` and an eigenmode `I • loopOperator T S a = λ • ι a`,
projecting `cylinderOperator T S u` onto `ι a` yields `s ↦ w'(s) + λ w(s)` a.e. for
`w(s) = ⟪ι a, (ι ∘ u)(s)⟫_ℝ`. -/
theorem compLpL_innerSL_cylinderOperator_ae_of_I_smul_loopOperator_eq_smul
    {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    {a : CircleSobolev 1 F} {lam : ℝ} (ha : I • loopOperator T S a = lam • inclusion zero_le_one a)
    (u : WeakDerivStep volume ⊤ 2
      (((inclusion (E := F) zero_le_one).restrictScalars ℝ).compLpL 2 μ₀)) :
    (innerSL ℝ (inclusion zero_le_one a)).compLpL 2 μ₀ (cylinderOperator T S u) =ᵐ[μ₀]
      fun s ↦ ⟪W1p.gradient (WeakDerivStep.toW1pL
            (((inclusion (E := F) zero_le_one).restrictScalars ℝ).compLpL 2 μ₀)
            (innerSL ℝ (inclusion zero_le_one a)) u) s, (1 : ℝ)⟫_ℝ +
        lam * W1p.value (WeakDerivStep.toW1pL
          (((inclusion (E := F) zero_le_one).restrictScalars ℝ).compLpL 2 μ₀)
          (innerSL ℝ (inclusion zero_le_one a)) u) s := by
  refine WeakDerivStep.compLpL_domainTrajectoryOperator_ae
    ((inclusion (E := F) zero_le_one).restrictScalars ℝ) (I • loopOperator T S)
    (innerSL ℝ (inclusion zero_le_one a)) (fun x ↦ ?_) u
  rw [innerSL_apply_apply, smul_apply, ← real_inner_I_smul_loopOperator_comm T S hS a x, ha,
    inner_smul_left, RCLike.conj_to_real, innerSL_apply_apply,
    ContinuousLinearMap.coe_restrictScalars']

end Symplectic

end TauCeti.CircleSobolev
