/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.Family
public import TauCeti.Analysis.Sobolev.GraphStep.AubinLions
public import TauCeti.Analysis.Sobolev.GraphStep.Multiplication
import TauCeti.Analysis.Normed.Operator.Compact.Estimate
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# The semi-Fredholm estimate for the trajectory operator over a compactly embedded domain

Let `ι : D →L[ℝ] H` embed a Banach space `D` into a Hilbert space `H`, and let
`A : ℝ → (D →L[ℝ] H)` be an essentially bounded family of operators, given as a class `AL` in
`L∞(ℝ, D →L[ℝ] H)`. The operator `D_A u = (ι ∘ u)' + A(s) u(s)` from `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)`
to `L²(ℝ, H)` is `TauCeti.WeakDerivStep.familyDomainTrajectoryOperator ι AL`. A typical case is
the linearized Floer operator on a strip or a cylinder in a unitary trivialization, where
`A(s) = J₀ ∂ₜ + S(s, t)` acts on loops or paths in `t`, with `D = H¹` and `H = L²`.

Suppose that `A(s)` converges to invertible `ι`-symmetric operators `B₋` and `B₊`
(`⟪B x, ι y⟫ = ⟪ι x, B y⟫`) as `s → -∞` and `s → ∞`, and that on every bounded interval `A(s)`
differs from `B₊` by an operator of lower order, bounded through `ι`: for every `T` there is `c`
with `‖(A(s) - B₊) x‖ ≤ c ‖ι x‖` for almost every `s ∈ (-T, T)`. For `A(s) = J₀ ∂ₜ + S(s, t)` and
`B₊ = J₀ ∂ₜ + S₊(t)` this is the bound of the multiplication operator `S(s, ·) - S₊` on `L²`. Then
the semi-Fredholm estimate

`‖u‖ ≤ C (‖D_A u‖ + ‖ι ∘ u‖_{L²((-T, T), H)})`

holds on the whole graph space, for some `C` and `T`
(`exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_norm_restrictBaseL`).
When `ι` is a compact operator, restricting `ι ∘ u` to `(-T, T)` is compact on the graph space by
the Aubin–Lions lemma `TauCeti.WeakDerivStep.isCompactOperator_restrictBaseL_compLpL`, so Peetre's
lemma gives that `D_A` has finite-dimensional kernel
(`TauCeti.WeakDerivStep.finiteDimensional_ker_familyDomainTrajectoryOperator`) and closed range
(`TauCeti.WeakDerivStep.isClosed_range_familyDomainTrajectoryOperator`). These are the first two
of the three properties making `D_A` Fredholm; the finite dimension of its cokernel is not proved
here.

The estimate is spliced from three pieces by smooth cutoffs `χ₋`, `χ₀ = 1 - χ₋ - χ₊` and `χ₊`
supported in `(-∞, -a]`, `[-a - 1, a + 1]` and `[a, ∞)`
(`TauCeti.exists_cutoffs_add_add_eq_one`). Multiplying a path by a cutoff `χ`
(`TauCeti.WeakDerivStep.smulLeftCLM`) changes `D_A` by the commutator term `χ' (ι ∘ u)`
(`TauCeti.WeakDerivStep.familyDomainTrajectoryOperator_smulLeftCLM_ae`), which lives on the window
where `χ'` is supported. On the two ends, `A(s)` is close to `B±`, and the estimate without error
term holds for paths supported there
(`exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto_atTop` and its `atBot`
version). In the middle, `D_A` differs from the invertible autonomous operator of
`B₊` by `A(s) - B₊`, whose action on a path supported in the window is bounded by `c` times the
`L²` norm of `ι ∘ u` there.

## Main results

* `TauCeti.WeakDerivStep.familyDomainTrajectoryOperator_smulLeftCLM_ae`: the commutator
  `D_A (χ u) = χ D_A u + χ' (ι ∘ u)` of `D_A` with a smooth cutoff `χ`.
* `exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_norm_restrictBaseL`: the
  semi-Fredholm estimate with the window error term.
* `TauCeti.WeakDerivStep.finiteDimensional_ker_familyDomainTrajectoryOperator`: for compact `ι`,
  the kernel of `D_A` is finite dimensional.
* `TauCeti.WeakDerivStep.isClosed_range_familyDomainTrajectoryOperator`: for compact `ι`, the range
  of `D_A` is closed.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33, §3 (the estimate `‖u‖ ≤ C (‖D_A u‖ + ‖u‖_{L²((-T, T), H)})` for a family
  of self-adjoint operators over a compactly embedded domain).
* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. **7** (1999), Lecture 2
  (the operators `∂ₛ + J₀ ∂ₜ + S(s, t)` and their Fredholm theory).
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open Filter _root_.MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology ContDiff

/-! ### The commutator with a cutoff -/

section Commutator

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup H]
  [NormedSpace ℝ H] [CompleteSpace H] {mu : Measure ℝ} [IsFiniteMeasureOnCompacts mu]
  {Omega : Opens ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {χ : ℝ → ℝ}

/-- **The commutator of the trajectory operator with a cutoff.** For `χ` smooth on `Ω` with `χ` and
`χ'` bounded there, `D_A (χ u) = χ D_A u + χ' (ι ∘ u)` almost everywhere. -/
theorem familyDomainTrajectoryOperator_smulLeftCLM_ae (ι : D →L[ℝ] H)
    (A : Lp (D →L[ℝ] H) ∞ (mu.restrict Omega)) (hχ : ContDiffOn ℝ ∞ χ Omega)
    (h₀ : ∃ C, ∀ s ∈ Omega, ‖χ s‖ ≤ C) (h₁ : ∃ C, ∀ s ∈ Omega, ‖fderiv ℝ χ s‖ ≤ C)
    (u : WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega))) :
    familyDomainTrajectoryOperator ι A
        (smulLeftCLM χ hχ h₀ h₁ ι.compLpL_multiplicationOperator u) =ᵐ[mu.restrict Omega]
      fun s ↦ χ s • familyDomainTrajectoryOperator ι A u s + deriv χ s • ι (prev _ u s) := by
  filter_upwards [familyDomainTrajectoryOperator_apply_ae ι A
      (smulLeftCLM χ hχ h₀ h₁ ι.compLpL_multiplicationOperator u),
    prev_smulLeftCLM_ae hχ h₀ h₁ ι.compLpL_multiplicationOperator u,
    weakFDeriv_smulLeftCLM_ae hχ h₀ h₁ ι.compLpL_multiplicationOperator u,
    familyDomainTrajectoryOperator_apply_ae ι A u, ι.coeFn_compLpL (prev _ u)]
    with s hD hp hd hDu hι
  rw [hD, hp, hd, hDu, hι, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, fderiv_apply_one_eq_deriv, (A s).map_smul, smul_add]
  abel

end Commutator

local notation "μ₀" => (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {ι : D →L[ℝ] H}

/-- Almost everywhere for `μ₀` is almost everywhere on the line. -/
private theorem ae_top_iff {P : ℝ → Prop} : (∀ᵐ s ∂μ₀, P s) ↔ ∀ᵐ s ∂volume, P s := by simp

/-! ### Multiplication by a cutoff -/

/-- The derivative bound of a cutoff on the line, in the form taken by `smulLeftCLM`. -/
private theorem exists_forall_norm_fderiv_le {χ : ℝ → ℝ} {C₁ : ℝ} (h : ∀ s, |deriv χ s| ≤ C₁) :
    ∃ C, ∀ s ∈ (⊤ : Opens ℝ), ‖fderiv ℝ χ s‖ ≤ C :=
  ⟨C₁, fun s _ ↦ by rw [← norm_deriv_eq_norm_fderiv]; exact h s⟩

omit [CompleteSpace D] in
/-- **The error of a cutoff.** If `|χ| ≤ 1`, `|χ'| ≤ C₁` and `χ'` vanishes off the window
`(-b, b)`, then `‖D_A (χ u)‖ ≤ ‖D_A u‖ + C₁ ‖ι ∘ u‖_{L²((-b, b), H)}`. -/
private theorem norm_familyDomainTrajectoryOperator_smulLeftCLM_le {χ : ℝ → ℝ}
    (hχ : ContDiffOn ℝ ∞ χ ((⊤ : Opens ℝ) : Set ℝ)) (h₀ : ∃ C, ∀ s ∈ (⊤ : Opens ℝ), ‖χ s‖ ≤ C)
    (h₁ : ∃ C, ∀ s ∈ (⊤ : Opens ℝ), ‖fderiv ℝ χ s‖ ≤ C) (hχ₀ : ∀ s, |χ s| ≤ 1) {C₁ b : ℝ}
    (hχ₁ : ∀ s, |deriv χ s| ≤ C₁) (hχ' : ∀ s ∉ Ioo (-b) b, deriv χ s = 0)
    (AL : Lp (D →L[ℝ] H) ∞ μ₀) (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    ‖familyDomainTrajectoryOperator ι AL
        (smulLeftCLM χ hχ h₀ h₁ ι.compLpL_multiplicationOperator u)‖ ≤
      ‖familyDomainTrajectoryOperator ι AL u‖ +
        C₁ * ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-b) b, isOpen_Ioo⟩) le_top u‖ := by
  have hC₁ : 0 ≤ C₁ := (abs_nonneg _).trans (hχ₁ 0)
  set f := familyDomainTrajectoryOperator ι AL
    (smulLeftCLM χ hχ h₀ h₁ ι.compLpL_multiplicationOperator u)
  set g := familyDomainTrajectoryOperator ι AL u
  -- `D_A (χ u)` is `χ D_A u` up to the commutator term `χ' (ι ∘ u)`.
  set m := Lp.multiplicationOperator
    (linftyOfContinuousOn volume hχ.continuousOn (⊤ : Opens ℝ).isOpen.measurableSet h₀) g
  have hm := Lp.multiplicationOperator_linftyOfContinuousOn_ae hχ.continuousOn
    (⊤ : Opens ℝ).isOpen.measurableSet h₀ g
  refine (norm_le_insert' f m).trans (add_le_add ?_ ?_)
  · refine (Lp.norm_le_mul_norm_of_ae_le_mul (c := 1) ?_).trans_eq (one_mul _)
    filter_upwards [hm] with s hs
    rw [hs, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hχ₀ s) (norm_nonneg _)
  · have hfm : ∀ᵐ s ∂volume, (f - m) s = deriv χ s • ι (prev _ u s) := by
      filter_upwards [ae_top_iff.1 (Lp.coeFn_sub f m),
        ae_top_iff.1 (familyDomainTrajectoryOperator_smulLeftCLM_ae ι AL hχ h₀ h₁ u),
        ae_top_iff.1 hm] with s h₁ h₂ h₃
      rw [h₁, Pi.sub_apply, h₂, h₃, add_sub_cancel_left]
    refine norm_le_mul_norm_restrictBaseL hC₁ u ?_ ?_
    · filter_upwards [hfm] with s hs
      rw [hs, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hχ₁ s) (norm_nonneg _)
    · filter_upwards [hfm] with s hs hsW
      rw [hs, hχ' s hsW, zero_smul]

/-! ### The middle piece -/

variable {B Bbot Btop : D →L[ℝ] H} {A : ℝ → D →L[ℝ] H} {AL : Lp (D →L[ℝ] H) ∞ μ₀} {c : ℝ}

/-- **The estimate on a window.** Let `A(s)` differ from an invertible `ι`-symmetric `B` by at most
`c ‖ι x‖` on the window `(-b, b)`, with `c ≥ 0`. A path `w = φ u`, for a weight `|φ| ≤ 1` vanishing
off the window, satisfies `‖w‖ ≤ M (‖D_A w‖ + c ‖ι ∘ u‖_{L²((-b, b), H)})` with
`M = √(1 + ‖B⁻¹‖²)`. -/
private theorem norm_le_of_ae_prev_eq_smul (hSymm : ∀ x y : D, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ)
    (hB : B.IsInvertible) (hAL : AL =ᵐ[μ₀] A) (hc₀ : 0 ≤ c) {b : ℝ}
    (hc : ∀ᵐ s ∂volume, s ∈ Ioo (-b) b → ∀ x, ‖(A s - B) x‖ ≤ c * ‖ι x‖) {φ : ℝ → ℝ}
    (hφ : ∀ s, |φ s| ≤ 1) (hφ₀ : ∀ s ∉ Ioo (-b) b, φ s = 0)
    {u w : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)}
    (hw : ∀ᵐ s ∂volume, prev _ w s = φ s • prev _ u s) :
    ‖w‖ ≤ √(1 + ‖B.inverse‖ ^ 2) * (‖familyDomainTrajectoryOperator ι AL w‖ +
      c * ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-b) b, isOpen_Ioo⟩) le_top u‖) := by
  -- `D_A w - D_B w = (A - B) w` is bounded by `c ‖ι ∘ u‖` on the window and vanishes off it.
  have hdiff : ‖familyDomainTrajectoryOperator ι AL w - domainTrajectoryOperator ι B w‖ ≤
      c * ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-b) b, isOpen_Ioo⟩) le_top u‖ := by
    have hm := ae_top_iff.1
      (familyDomainTrajectoryOperator_sub_domainTrajectoryOperator_ae ι AL B w)
    refine norm_le_mul_norm_restrictBaseL hc₀ u ?_ ?_
    · filter_upwards [hm, ae_top_iff.1 hAL, hc, hw] with s h₁ h₂ h₃ h₄
      rw [h₁, h₂, h₄, map_smul, norm_smul, Real.norm_eq_abs]
      by_cases hsW : s ∈ Ioo (-b) b
      · exact (mul_le_mul (hφ s) (h₃ hsW _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      · rw [hφ₀ s hsW, abs_zero, zero_mul]
        exact mul_nonneg hc₀ (norm_nonneg _)
    · filter_upwards [hm, hw] with s h₁ h₂ hsW
      rw [h₁, h₂, hφ₀ s hsW, zero_smul, map_zero]
  refine (norm_le_sqrt_one_add_sq_mul_norm_domainTrajectoryOperator hSymm hB w).trans ?_
  gcongr
  have := norm_sub_norm_le (domainTrajectoryOperator ι B w) (familyDomainTrajectoryOperator ι AL w)
  rw [norm_sub_rev] at this
  linarith

omit [CompleteSpace D] in
/-- **An end piece.** If `‖w‖ ≤ C ‖D_A w‖` for every path `w` vanishing on `S`, then a path
`w = φ u` with `φ = 0` on `S` and `‖D_A w‖ ≤ X` satisfies `‖w‖ ≤ max C 0 * X`. -/
private theorem norm_le_max_mul_of_ae_prev_eq_smul {S : Set ℝ} {C X : ℝ}
    (hC : ∀ w : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      (∀ᵐ s ∂volume, s ∈ S → prev _ w s = 0) → ‖w‖ ≤ C * ‖familyDomainTrajectoryOperator ι AL w‖)
    {φ : ℝ → ℝ} (hφ : ∀ s ∈ S, φ s = 0) {u w : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)}
    (hw : ∀ᵐ s ∂volume, prev _ w s = φ s • prev _ u s)
    (hX : ‖familyDomainTrajectoryOperator ι AL w‖ ≤ X) : ‖w‖ ≤ max C 0 * X := by
  refine (hC w ?_).trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hX (le_max_right _ _)))
  filter_upwards [hw] with s hs hsS
  rw [hs, hφ s hsS, zero_smul]

omit [CompleteSpace D] in
/-- The middle piece `u - w₁ - w₂` of the paths `w₁ = φ u` and `w₂ = ψ u` is `(1 - φ - ψ) u`. -/
private theorem ae_prev_sub_sub_eq_smul {φ ψ : ℝ → ℝ}
    {u w₁ w₂ : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)}
    (h₁ : ∀ᵐ s ∂volume, prev _ w₁ s = φ s • prev _ u s)
    (h₂ : ∀ᵐ s ∂volume, prev _ w₂ s = ψ s • prev _ u s) :
    ∀ᵐ s ∂volume, prev _ (u - w₁ - w₂) s = (1 - φ s - ψ s) • prev _ u s := by
  filter_upwards [ae_top_iff.1 (Lp.coeFn_sub (prev _ u - prev _ w₁) (prev _ w₂)),
    ae_top_iff.1 (Lp.coeFn_sub (prev _ u) (prev _ w₁)), h₁, h₂] with s hs hs' hs₁ hs₂
  rw [← prevL_apply, map_sub, map_sub, prevL_apply, prevL_apply, prevL_apply, hs, Pi.sub_apply,
    hs', Pi.sub_apply, hs₁, hs₂, sub_smul, sub_smul, one_smul]

/-! ### The estimate -/

/-- **Splicing the three pieces.** Let `D_A` satisfy `‖w‖ ≤ C₊ ‖D_A w‖` for the paths vanishing on
`(-∞, T₊)` and `‖w‖ ≤ C₋ ‖D_A w‖` for those vanishing on `(T₋, ∞)`, and let `A(s)` differ from an
invertible `ι`-symmetric `B` by at most `c ‖ι x‖` on `(-(a + 2), a + 2)`. For `a ≥ max T₊ (-T₋)`,
cutting a path `u` by the cutoffs `βp`, `βm` and `β₀` of `TauCeti.exists_cutoffs_add_add_eq_one`
bounds it by `‖D_A u‖` and the `L²` norm `R` of `ι ∘ u` on `(-(a + 2), a + 2)`. -/
private theorem norm_le_of_end_estimates (hSymm : ∀ x y : D, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ)
    (hB : B.IsInvertible) (hAL : AL =ᵐ[μ₀] A) (hc₀ : 0 ≤ c) {Ctop Cbot Ttop Tbot a L : ℝ}
    (hc : ∀ᵐ s ∂volume, s ∈ Ioo (-(a + 2)) (a + 2) → ∀ x, ‖(A s - B) x‖ ≤ c * ‖ι x‖)
    (hCtop : ∀ w : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      (∀ᵐ s ∂volume, s < Ttop → prev _ w s = 0) →
        ‖w‖ ≤ Ctop * ‖familyDomainTrajectoryOperator ι AL w‖)
    (hCbot : ∀ w : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      (∀ᵐ s ∂volume, Tbot < s → prev _ w s = 0) →
        ‖w‖ ≤ Cbot * ‖familyDomainTrajectoryOperator ι AL w‖)
    (haT : Ttop ≤ a) (haT' : -Tbot ≤ a) {βp βm β₀ : ℝ → ℝ} (hsum : ∀ s, βp s + βm s + β₀ s = 1)
    (hβp : ∀ s, s ≤ a → βp s = 0) (hβm : ∀ s, -a ≤ s → βm s = 0)
    (hβ₀ : ∀ s, s ∉ Ioo (-(a + 1)) (a + 1) → β₀ s = 0)
    (hβ : ∀ β ∈ ({βp, βm, β₀} : Set (ℝ → ℝ)), ContDiff ℝ ∞ β ∧ (∀ s, |β s| ≤ 1) ∧
      (∀ s, |deriv β s| ≤ L) ∧ ∀ s, s < -(a + 1) ∨ a + 1 < s → deriv β s = 0)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    ‖u‖ ≤ (max Ctop 0 + max Cbot 0) * (‖familyDomainTrajectoryOperator ι AL u‖ + L *
        ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-(a + 2)) (a + 2), isOpen_Ioo⟩) le_top u‖) +
      √(1 + ‖B.inverse‖ ^ 2) * (3 * ‖familyDomainTrajectoryOperator ι AL u‖ + (2 * L + c) *
        ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-(a + 2)) (a + 2), isOpen_Ioo⟩) le_top u‖) := by
  set R := ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-(a + 2)) (a + 2), isOpen_Ioo⟩) le_top u‖
  set N := ‖familyDomainTrajectoryOperator ι AL u‖
  obtain ⟨hpc, hp1, hpL, hpT⟩ := hβ βp (by simp)
  obtain ⟨hmc, hm1, hmL, hmT⟩ := hβ βm (by simp)
  obtain ⟨-, h01, -, -⟩ := hβ β₀ (by simp)
  have hwin (s : ℝ) (hs : s ∉ Ioo (-(a + 2)) (a + 2)) : s < -(a + 1) ∨ a + 1 < s := by
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hs
    rcases hs with hs | hs
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  set wtop := smulLeftCLM βp hpc.contDiffOn ⟨1, fun s _ ↦ hp1 s⟩ (exists_forall_norm_fderiv_le hpL)
    ι.compLpL_multiplicationOperator u
  set wbot := smulLeftCLM βm hmc.contDiffOn ⟨1, fun s _ ↦ hm1 s⟩ (exists_forall_norm_fderiv_le hmL)
    ι.compLpL_multiplicationOperator u
  have hptop := ae_top_iff.1 (prev_smulLeftCLM_ae hpc.contDiffOn ⟨1, fun s _ ↦ hp1 s⟩
    (exists_forall_norm_fderiv_le hpL) ι.compLpL_multiplicationOperator u)
  have hpbot := ae_top_iff.1 (prev_smulLeftCLM_ae hmc.contDiffOn ⟨1, fun s _ ↦ hm1 s⟩
    (exists_forall_norm_fderiv_le hmL) ι.compLpL_multiplicationOperator u)
  -- The two ends `w₊ = βp u` and `w₋ = βm u`.
  have hDtop : ‖familyDomainTrajectoryOperator ι AL wtop‖ ≤ N + L * R :=
    norm_familyDomainTrajectoryOperator_smulLeftCLM_le _ _ _ hp1 hpL
      (fun s hs ↦ hpT s (hwin s hs)) _ u
  have hDbot : ‖familyDomainTrajectoryOperator ι AL wbot‖ ≤ N + L * R :=
    norm_familyDomainTrajectoryOperator_smulLeftCLM_le _ _ _ hm1 hmL
      (fun s hs ↦ hmT s (hwin s hs)) _ u
  have hwtop := norm_le_max_mul_of_ae_prev_eq_smul (S := Iio Ttop) hCtop
    (fun s hs ↦ hβp s (by linarith [mem_Iio.1 hs])) hptop hDtop
  have hwbot := norm_le_max_mul_of_ae_prev_eq_smul (S := Ioi Tbot) hCbot
    (fun s hs ↦ hβm s (by linarith [mem_Ioi.1 hs])) hpbot hDbot
  -- The middle `u - w₋ - w₊ = (1 - βm - βp) u = β₀ u`.
  have h₀ (s : ℝ) : 1 - βm s - βp s = β₀ s := by linarith [hsum s]
  have hw₀ := norm_le_of_ae_prev_eq_smul hSymm hB hAL hc₀ hc (fun s ↦ h₀ s ▸ h01 s)
    (fun s hs ↦ (h₀ s).trans (hβ₀ s fun h ↦ hs ⟨by linarith [h.1], by linarith [h.2]⟩))
    (ae_prev_sub_sub_eq_smul hpbot hptop)
  have hD₀ : ‖familyDomainTrajectoryOperator ι AL (u - wbot - wtop)‖ ≤ 3 * N + 2 * L * R := by
    rw [map_sub, map_sub]
    linarith [norm_sub_le (familyDomainTrajectoryOperator ι AL u -
      familyDomainTrajectoryOperator ι AL wbot) (familyDomainTrajectoryOperator ι AL wtop),
      norm_sub_le (familyDomainTrajectoryOperator ι AL u)
        (familyDomainTrajectoryOperator ι AL wbot)]
  have htri : ‖u‖ ≤ ‖wbot‖ + ‖u - wbot - wtop‖ + ‖wtop‖ := by
    calc ‖u‖ = ‖wbot + (u - wbot - wtop) + wtop‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hM := mul_le_mul_of_nonneg_left hD₀ (Real.sqrt_nonneg (1 + ‖B.inverse‖ ^ 2))
  linarith [hwtop, hwbot, hw₀, hM, htri]

/-- **The semi-Fredholm estimate for the trajectory operator over a common domain.** Let `A(s)`
converge to invertible `ι`-symmetric operators `Bbot` and `Btop` at `-∞` and `∞`, and differ from
`Btop` on every bounded interval by an operator bounded through `ι`: for every `T` there is `c` with
`‖(A(s) - Btop) x‖ ≤ c ‖ι x‖` for almost every `s ∈ (-T, T)`. Then there are `C` and `T` with

`‖u‖ ≤ C (‖(ι ∘ u)' + A u‖ + ‖ι ∘ u‖_{L²((-T, T), H)})`

for every `u ∈ L²(ℝ, D) ∩ W^{1,2}(ℝ, H)`. -/
theorem exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_norm_restrictBaseL
    (hSymmbot : ∀ x y : D, ⟪Bbot x, ι y⟫_ℝ = ⟪ι x, Bbot y⟫_ℝ) (hBbot : Bbot.IsInvertible)
    (hSymmtop : ∀ x y : D, ⟪Btop x, ι y⟫_ℝ = ⟪ι x, Btop y⟫_ℝ) (hBtop : Btop.IsInvertible)
    (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    ∃ C T : ℝ, ∀ u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      ‖u‖ ≤ C * (‖familyDomainTrajectoryOperator ι AL u‖ +
        ‖restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-T) T, isOpen_Ioo⟩) le_top u‖) := by
  obtain ⟨Cbot, Tbot, hCbot⟩ :=
    exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto_atBot
      hSymmbot hBbot hAL hbot
  obtain ⟨Ctop, Ttop, hCtop⟩ :=
    exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto_atTop
      hSymmtop hBtop hAL htop
  set a := max (max Ttop (-Tbot)) 0
  obtain ⟨L, βp, βm, β₀, hsum, hβp, hβm, hβ₀, hβ⟩ :=
    exists_cutoffs_add_add_eq_one (le_max_right _ _ : (0 : ℝ) ≤ a)
  have hL₀ : 0 ≤ L := (abs_nonneg _).trans ((hβ βp (by simp)).2.2.1 0)
  obtain ⟨c, hc⟩ := hc (a + 2)
  have hc' : ∀ᵐ s ∂volume, s ∈ Ioo (-(a + 2)) (a + 2) →
      ∀ x, ‖(A s - Btop) x‖ ≤ max c 0 * ‖ι x‖ := by
    filter_upwards [hc] with s hs hsW x
    exact (hs hsW x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  set K := max Ctop 0 + max Cbot 0
  set M := √(1 + ‖Btop.inverse‖ ^ 2)
  refine ⟨K * (1 + L) + M * (3 + 2 * L + max c 0), a + 2, fun u ↦ ?_⟩
  have h := norm_le_of_end_estimates hSymmtop hBtop hAL (le_max_right c 0) hc' hCtop hCbot
    ((le_max_left _ _).trans (le_max_left _ _)) ((le_max_right _ _).trans (le_max_left _ _))
    hsum hβp hβm hβ₀ hβ u
  -- Every coefficient is at most the constant, since all the terms are nonnegative.
  have hK : 0 ≤ K := add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have hN := norm_nonneg (familyDomainTrajectoryOperator ι AL u)
  have hR := norm_nonneg
    (restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-(a + 2)) (a + 2), isOpen_Ioo⟩) le_top u)
  linarith [h, mul_nonneg (mul_nonneg hK hL₀) hN, mul_nonneg hK hR,
    mul_nonneg (mul_nonneg hM hL₀) hN, mul_nonneg (mul_nonneg hM (le_max_right c 0)) hN,
    mul_nonneg hM hR]

/-- The semi-Fredholm estimate in the form of Peetre's lemma: for compact `ι`, there is a compact
operator `K` on the graph space with `‖u‖ ≤ C ‖D_A u‖ + ‖K u‖`. -/
private theorem exists_isCompactOperator_and_norm_le (hι : IsCompactOperator ι)
    (hSymmbot : ∀ x y : D, ⟪Bbot x, ι y⟫_ℝ = ⟪ι x, Bbot y⟫_ℝ) (hBbot : Bbot.IsInvertible)
    (hSymmtop : ∀ x y : D, ⟪Btop x, ι y⟫_ℝ = ⟪ι x, Btop y⟫_ℝ) (hBtop : Btop.IsInvertible)
    (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    ∃ (T C : ℝ) (K : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀) →L[ℝ]
      Lp H 2 (volume.restrict (Ioo (-T) T))), IsCompactOperator K ∧
        ∀ u, ‖u‖ ≤ C * ‖familyDomainTrajectoryOperator ι AL u‖ + ‖K u‖ := by
  obtain ⟨C, T, hC⟩ :=
    exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_norm_restrictBaseL
      hSymmbot hBbot hSymmtop hBtop hAL hbot htop hc
  set R := restrictBaseL (ι.compLpL 2 μ₀) (V := ⟨Ioo (-T) T, isOpen_Ioo⟩) le_top
  refine ⟨T, C, C • R, ?_, fun u ↦ ?_⟩
  · rw [FunLike.coe_smul]
    exact (isCompactOperator_restrictBaseL_compLpL hι _).smul C
  · rw [smul_apply, norm_smul, Real.norm_eq_abs]
    linarith [hC u, mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg (R u))]

/-- **The kernel of the trajectory operator over a compactly embedded domain is finite
dimensional.** Under the hypotheses of
`exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_norm_restrictBaseL`, if moreover
`ι` is a compact operator, the kernel of `u ↦ (ι ∘ u)' + A u` on `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` is
finite dimensional. -/
theorem finiteDimensional_ker_familyDomainTrajectoryOperator (hι : IsCompactOperator ι)
    (hSymmbot : ∀ x y : D, ⟪Bbot x, ι y⟫_ℝ = ⟪ι x, Bbot y⟫_ℝ) (hBbot : Bbot.IsInvertible)
    (hSymmtop : ∀ x y : D, ⟪Btop x, ι y⟫_ℝ = ⟪ι x, Btop y⟫_ℝ) (hBtop : Btop.IsInvertible)
    (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    FiniteDimensional ℝ (familyDomainTrajectoryOperator (p := 2) ι AL).ker := by
  obtain ⟨T, C, K, hK, hCK⟩ := exists_isCompactOperator_and_norm_le hι hSymmbot hBbot hSymmtop
    hBtop hAL hbot htop hc
  exact (familyDomainTrajectoryOperator ι AL).finiteDimensional_ker_of_compact_estimate hK hCK

/-- **The range of the trajectory operator over a compactly embedded domain is closed.** Under the
hypotheses of
`exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_add_norm_restrictBaseL`, if moreover
`ι` is a compact operator, the range of `u ↦ (ι ∘ u)' + A u` from `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` to
`L²(ℝ, H)` is closed. -/
theorem isClosed_range_familyDomainTrajectoryOperator (hι : IsCompactOperator ι)
    (hSymmbot : ∀ x y : D, ⟪Bbot x, ι y⟫_ℝ = ⟪ι x, Bbot y⟫_ℝ) (hBbot : Bbot.IsInvertible)
    (hSymmtop : ∀ x y : D, ⟪Btop x, ι y⟫_ℝ = ⟪ι x, Btop y⟫_ℝ) (hBtop : Btop.IsInvertible)
    (hAL : AL =ᵐ[μ₀] A) (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    IsClosed ((familyDomainTrajectoryOperator (p := 2) ι AL).range : Set (Lp H 2 μ₀)) := by
  obtain ⟨T, C, K, hK, hCK⟩ := exists_isCompactOperator_and_norm_le hι hSymmbot hBbot hSymmtop
    hBtop hAL hbot htop hc
  exact (familyDomainTrajectoryOperator ι AL).isClosed_range_of_compact_estimate hK hCK

end TauCeti.WeakDerivStep
