/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.Density
public import TauCeti.Analysis.Sobolev.GraphStep.ZeroAtInfty
public import TauCeti.Analysis.Fredholm.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Basic
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.Basic
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The autonomous trajectory operator over a common domain

Let `D` be a real Banach space continuously mapped into a real Banach or Hilbert space `H` by
`ι : D →L[ℝ] H`, and let `A : D →L[ℝ] H` be a bounded linear operator. Typical examples are
first-order elliptic operators on compact slices, such as the periodic asymptotic operator
`A : H¹(S¹, F) →L[ℝ] H⁰(S¹, F)` along `ι : H¹(S¹, F) →L[ℝ] H⁰(S¹, F)`. On an open set `Ω ⊆ ℝ`,
the existing graph space

`WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega))`

is the intersection `Lᵖ(Ω, D) ∩ W^{1,p}(Ω, H)` of `D`-valued `Lᵖ` paths whose `H`-valued image
`ι ∘ u` has an `Lᵖ` weak derivative, with squared norm `‖u‖²_{Lᵖ(Ω, D)} + ‖(ι ∘ u)'‖²_{Lᵖ(Ω, H)}`.
No new Sobolev carrier is introduced.

This file realizes `∂s ∘ ι + A` on that graph space as the bounded linear operator
`TauCeti.WeakDerivStep.domainTrajectoryOperator ι A` into `Lᵖ(Ω, H)`, proves its basic Lipschitz
and weak-ODE properties together with scalar mode injection and projection, and establishes its
invertibility theory on the whole line `Ω = ⊤` for `p = 2` when `H` is a Hilbert space and `A` is
`ι`-symmetric (`⟪A x, ι y⟫ = ⟪ι x, A y⟫`):

* **Whole-line orthogonality and Pythagorean identity.** Applying the weak product rule
  `TauCeti.HasWeakLineDerivOn.bilin_self` to the symmetric bilinear form `(x, y) ↦ ⟪ι x, A y⟫` on
  `D` shows that `s ↦ ⟪ι (u s), A (u s)⟫` belongs to `W^{1,1}(ℝ)` with weak derivative
  `2 ⟪(ι ∘ u)' s, A (u s)⟫`, whose whole-line integral vanishes
  (`TauCeti.HasWeakLineDerivOn.integral_eq_zero_of_integrable`). Hence `(ι ∘ u)'` and `A ∘ u` are
  orthogonal in `L²(ℝ, H)`, and `‖(∂s ∘ ι + A) u‖² = ‖(ι ∘ u)'‖² + ‖A ∘ u‖²`.
* **Injectivity without invertibility of `A`.** When `ι` is injective, any element in the kernel of
  `∂s ∘ ι + A` has `(ι ∘ u)' = 0`; since `ι ∘ u ∈ W^{1,2}(ℝ, H)` vanishes at infinity, `u = 0`,
  even if `A` has a nontrivial kernel.
* **Invertibility and coercive inverse bound.** When `A` is invertible, the Pythagorean identity
  yields `‖u‖ ≤ √(1 + ‖A⁻¹‖²) ‖(∂s ∘ ι + A) u‖`, so `∂s ∘ ι + A` has closed range. A vector
  `v ∈ L²(ℝ, H)` orthogonal to the range pairs to zero against `φ(s) • A⁻¹ h` for all test
  functions `φ` and `h ∈ H`, which implies that `w = A⁻¹ ∘ v` lies in the domain with
  `(ι ∘ w)' = v` and `A ∘ w = v`; orthogonality on `w` gives `‖v‖² = 0`, so `∂s ∘ ι + A` is
  surjective, hence a continuous linear isomorphism with inverse norm at most `√(1 + ‖A⁻¹‖²)`.
* **Sharpness of invertibility of `A`.** Conversely, if `ι` is injective and `A.ker ≠ ⊥`, smooth
  plateau profiles (`TauCeti.exists_forall_contDiff_plateau`) along a nonzero kernel vector violate
  the open-mapping lower bound, so the range of `∂s ∘ ι + A` is not closed (in particular
  `∂s ∘ ι + A` is not Fredholm). When `A` is Fredholm of index zero, closed range, Fredholmness,
  and invertibility of `∂s ∘ ι + A` are each equivalent to invertibility of `A`.

The operator API adapts `TauCeti.WeakDerivStep.trajectoryOperator`
(`TauCeti/Analysis/ODE/TrajectoryOperator.lean`) from `ι = id` to a general domain map `ι`, using
`TauCeti.WeakDerivStep.smulRightBaseW1pL` (adapted from `TauCeti.WeakDerivStep.smulRightW1pL` in
`TauCeti/Analysis/Sobolev/GraphStep/Density.lean`); the orthogonal-range test-function argument and
approximate-kernel non-closed-range argument adapt those in
`TauCeti/Analysis/ODE/EnergyEstimate/Cokernel.lean` and
`TauCeti/Analysis/ODE/TrajectoryOperator/Degenerate.lean`.

## Main declarations

* `TauCeti.WeakDerivStep.domainTrajectoryOperator`: the bounded operator `∂s ∘ ι + A`.
* `TauCeti.WeakDerivStep.domainTrajectoryOperator_smulRightBaseW1pL_ae`: action of `∂s ∘ ι + A` on
  a single scalar mode `s ↦ w s • a`.
* `TauCeti.WeakDerivStep.compLpL_domainTrajectoryOperator_ae`: mode projection of `∂s ∘ ι + A`
  along a continuous linear functional `ℓ : H →L[ℝ] ℝ` satisfying `ℓ (A x) = λ * ℓ (ι x)`.
* `TauCeti.WeakDerivStep.inner_weakFDeriv_apply_one_compLpL_eq_zero`,
  `TauCeti.WeakDerivStep.norm_domainTrajectoryOperator_sq`: whole-line `L²` orthogonality and the
  Pythagorean identity `‖(∂s ∘ ι + A) u‖² = ‖(ι ∘ u)'‖² + ‖A ∘ u‖²`.
* `TauCeti.WeakDerivStep.injective_domainTrajectoryOperator_of_symmetric`: injectivity of
  `∂s ∘ ι + A` for injective `ι` and `ι`-symmetric `A`.
* `TauCeti.WeakDerivStep.isInvertible_domainTrajectoryOperator`,
  `TauCeti.WeakDerivStep.norm_inverse_domainTrajectoryOperator_le`: invertibility and explicit
  inverse-norm bound `√(1 + ‖A.inverse‖²)` when `A` is invertible.
* `TauCeti.WeakDerivStep.not_isClosed_range_domainTrajectoryOperator_of_ker_ne_bot`,
  `TauCeti.WeakDerivStep.isClosed_range_domainTrajectoryOperator_iff`,
  `TauCeti.WeakDerivStep.isFredholm_domainTrajectoryOperator_iff`,
  `TauCeti.WeakDerivStep.isInvertible_domainTrajectoryOperator_iff`: non-closed range when
  `A.ker ≠ ⊥`, and the equivalences with `A.IsInvertible` when `A` is Fredholm of index zero.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33, §2 and §4 (the operator `d/ds + A` on `W^{1,2}(ℝ, H) ∩ L²(ℝ, W)`, its `L²`
  integration by parts, and invertibility when `A` is invertible).
* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. **7** (1999), Lecture 2.
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open Filter _root_.MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Gradient InnerProductSpace Topology

section Banach

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {mu : Measure ℝ} [IsFiniteMeasureOnCompacts mu] {Omega : Opens ℝ}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The autonomous first-order operator `u ↦ (ι ∘ u)' + A ∘ u` from the common-domain Sobolev
graph `Lᵖ(Ω, D) ∩ W^{1,p}(Ω, H)` to `Lᵖ(Ω, H)`. -/
def domainTrajectoryOperator (ι A : D →L[ℝ] H) :
    WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega)) →L[ℝ] Lp H p (mu.restrict Omega) :=
  ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p (mu.restrict Omega)).comp
      (weakFDerivL (ι.compLpL p (mu.restrict Omega))) +
    (A.compLpL p (mu.restrict Omega)).comp (prevL (ι.compLpL p (mu.restrict Omega)))

/-- Unfolding formula for `domainTrajectoryOperator` as a continuous linear map. -/
theorem domainTrajectoryOperator_def (ι A : D →L[ℝ] H) :
    domainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι A =
      ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p (mu.restrict Omega)).comp
          (weakFDerivL (ι.compLpL p (mu.restrict Omega))) +
        (A.compLpL p (mu.restrict Omega)).comp (prevL (ι.compLpL p (mu.restrict Omega))) :=
  (rfl)

/-- `domainTrajectoryOperator` is the sum of evaluation of the weak derivative at `1` and
postcomposition of the value with `A`. -/
@[simp]
theorem domainTrajectoryOperator_apply (ι A : D →L[ℝ] H)
    (u : WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega))) :
    domainTrajectoryOperator ι A u =
      (ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p (mu.restrict Omega)
        (weakFDeriv (ι.compLpL p (mu.restrict Omega)) u) +
      A.compLpL p (mu.restrict Omega) (prev (ι.compLpL p (mu.restrict Omega)) u) := by
  simp [domainTrajectoryOperator]

/-- Pointwise almost-everywhere formula for `domainTrajectoryOperator`. -/
theorem domainTrajectoryOperator_apply_ae (ι A : D →L[ℝ] H)
    (u : WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega))) :
    domainTrajectoryOperator ι A u =ᵐ[mu.restrict Omega] fun s ↦
      weakFDeriv (ι.compLpL p (mu.restrict Omega)) u s 1 +
        A (prev (ι.compLpL p (mu.restrict Omega)) u s) := by
  let base := ι.compLpL p (mu.restrict Omega)
  let ev := (ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p (mu.restrict Omega)
  rw [domainTrajectoryOperator_apply]
  filter_upwards [Lp.coeFn_add (ev (weakFDeriv base u))
      (A.compLpL p (mu.restrict Omega) (prev base u)),
    (ContinuousLinearMap.apply ℝ H (1 : ℝ)).coeFn_compLpL (weakFDeriv base u),
    A.coeFn_compLpL (prev base u)] with s hadd hd hA
  rw [hadd, Pi.add_apply, hd, hA, ContinuousLinearMap.apply_apply]

/-- The operator norm of `domainTrajectoryOperator ι A` is at most `1 + ‖A‖`. -/
theorem norm_domainTrajectoryOperator_le (ι A : D →L[ℝ] H) :
    ‖domainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι A‖ ≤ 1 + ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
  let base := ι.compLpL p (mu.restrict Omega)
  rw [domainTrajectoryOperator_apply]
  calc
    ‖(ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p (mu.restrict Omega) (weakFDeriv base u) +
        A.compLpL p (mu.restrict Omega) (prev base u)‖
      ≤ ‖weakFDeriv base u‖ + ‖A.compLpL p (mu.restrict Omega) (prev base u)‖ :=
        (norm_add_le _ _).trans_eq (by rw [ContinuousLinearMap.norm_apply_one_compLpL])
    _ ≤ ‖u‖ + ‖A‖ * ‖u‖ := by
        refine add_le_add (norm_weakFDeriv_le base u) ?_
        refine ((A.compLpL p (mu.restrict Omega)).le_opNorm _).trans ?_
        gcongr
        · exact A.norm_compLpL_le
        · exact norm_prev_le base u
    _ = (1 + ‖A‖) * ‖u‖ := by ring

/-- Subtracting two operators over the same domain embedding cancels the derivative part. -/
theorem domainTrajectoryOperator_sub (ι A B : D →L[ℝ] H) :
    domainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι A -
      domainTrajectoryOperator ι B =
        ((A - B).compLpL p (mu.restrict Omega)).comp
          (prevL (ι.compLpL p (mu.restrict Omega))) := by
  ext u : 1
  simp only [sub_apply, domainTrajectoryOperator_apply,
    ContinuousLinearMap.comp_apply, prevL_apply, add_sub_add_left_eq_sub]
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (A.compLpL p (mu.restrict Omega) (prev _ u))
      (B.compLpL p (mu.restrict Omega) (prev _ u)),
    A.coeFn_compLpL (prev _ u), B.coeFn_compLpL (prev _ u),
    (A - B).coeFn_compLpL (prev _ u)] with s hsub hA hB hAB
  rw [hsub, Pi.sub_apply, hA, hB, hAB, sub_apply]

/-- Changing `A` to `B` changes `domainTrajectoryOperator ι` by at most `‖A - B‖` in operator
norm. -/
theorem norm_domainTrajectoryOperator_sub_le (ι A B : D →L[ℝ] H) :
    ‖domainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι A -
      domainTrajectoryOperator ι B‖ ≤ ‖A - B‖ := by
  rw [domainTrajectoryOperator_sub]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u ↦ ?_
  simp only [ContinuousLinearMap.comp_apply, prevL_apply]
  refine (((A - B).compLpL p (mu.restrict Omega)).le_opNorm _).trans ?_
  calc
    ‖(A - B).compLpL p (mu.restrict Omega)‖ * ‖prev _ u‖
      ≤ ‖A - B‖ * ‖u‖ := by
        gcongr
        · exact (A - B).norm_compLpL_le
        · exact norm_prev_le _ u

/-- `domainTrajectoryOperator ι` is `1`-Lipschitz in its zero-order operator `A`. -/
theorem lipschitzWith_domainTrajectoryOperator (ι : D →L[ℝ] H) :
    LipschitzWith 1 (domainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι) :=
  LipschitzWith.of_dist_le_mul fun A B ↦ by
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
      norm_domainTrajectoryOperator_sub_le ι A B

/-- `domainTrajectoryOperator ι` depends continuously on its zero-order operator `A`. -/
@[fun_prop]
theorem continuous_domainTrajectoryOperator (ι : D →L[ℝ] H) :
    Continuous (domainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι) :=
  (lipschitzWith_domainTrajectoryOperator ι).continuous

/-- Solving `domainTrajectoryOperator ι A u = f` is equivalent to solving the weak differential
equation `(ι ∘ u)' = f - A ∘ u`. -/
theorem domainTrajectoryOperator_eq_iff_hasWeakLineDerivOn (ι A : D →L[ℝ] H)
    (u : WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega)))
    (f : Lp H p (mu.restrict Omega)) :
    domainTrajectoryOperator ι A u = f ↔ HasWeakLineDerivOn mu Omega
      (ι.compLpL p (mu.restrict Omega) (prev (ι.compLpL p (mu.restrict Omega)) u))
      (fun s ↦ f s - A (prev (ι.compLpL p (mu.restrict Omega)) u s)) 1 := by
  let base := ι.compLpL p (mu.restrict Omega)
  have hd : HasWeakLineDerivOn mu Omega (base (prev base u)) (fun s ↦ weakFDeriv base u s 1) 1 :=
    (hasWeakFDerivOn_base_prev base u).hasWeakLineDerivOn 1
  constructor
  · intro h
    refine hd.congr_ae_deriv ?_
    have hform := domainTrajectoryOperator_apply_ae ι A u
    rw [h] at hform
    filter_upwards [hform] with s hs
    exact eq_sub_iff_add_eq.mpr hs.symm
  · intro h
    apply Lp.ext
    filter_upwards [domainTrajectoryOperator_apply_ae ι A u, hd.ae_eq h] with s hs hd'
    rw [hs, hd', sub_add_cancel]

/-- **Weak solutions define graph elements.** If `x ∈ Lᵖ(Ω, D)` satisfies `(ι ∘ x)' = f - A ∘ x`
weakly on `Ω`, then `x` is the value of a graph element `u` solving
`domainTrajectoryOperator ι A u = f`. -/
theorem exists_prev_eq_and_domainTrajectoryOperator_eq_of_hasWeakLineDerivOn (ι A : D →L[ℝ] H)
    {x : Lp D p (mu.restrict Omega)} {f : Lp H p (mu.restrict Omega)}
    (h : HasWeakLineDerivOn mu Omega (ι.compLpL p (mu.restrict Omega) x)
      (fun s ↦ f s - A (x s)) 1) :
    ∃ u : WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega)),
      prev (ι.compLpL p (mu.restrict Omega)) u = x ∧ domainTrajectoryOperator ι A u = f := by
  let g := f - A.compLpL p (mu.restrict Omega) x
  have hg : (fun s ↦ f s - A (x s)) =ᵐ[mu.restrict Omega] g := by
    filter_upwards [Lp.coeFn_sub f (A.compLpL p (mu.restrict Omega) x),
      A.coeFn_compLpL x] with s hs hAs
    simp only [g, hs, Pi.sub_apply, hAs]
  refine ⟨mkLine _ x g (h.congr_ae_deriv hg), prev_mkLine _ _ _ _, ?_⟩
  rw [domainTrajectoryOperator_eq_iff_hasWeakLineDerivOn, prev_mkLine]
  exact h

end Banach

/-! ### Scalar mode injection and projection -/

section Modes

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {mu : Measure ℝ} [mu.IsAddHaarMeasure] {Omega : Opens ℝ}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On a single mode `s ↦ w s • a`, `domainTrajectoryOperator ι A` acts as
`s ↦ w' s • ι a + w s • A a`. When `A a = λ • ι a`, this is `(w' s + λ w s) • ι a`. -/
theorem domainTrajectoryOperator_smulRightBaseW1pL_ae (ι A : D →L[ℝ] H) (a : D)
    (w : W1p mu Omega p) :
    domainTrajectoryOperator ι A (smulRightBaseW1pL ι a w) =ᵐ[mu.restrict Omega]
      fun s ↦ ⟪W1p.gradient w s, (1 : ℝ)⟫_ℝ • ι a + W1p.value w s • A a := by
  filter_upwards [domainTrajectoryOperator_apply_ae ι A (smulRightBaseW1pL ι a w),
    (smulRightGradientL (ι a)).coeFn_compLpL (W1p.gradient w),
    (ContinuousLinearMap.toSpanSingleton ℝ a).coeFn_compLpL (W1p.value w)] with s hD hg hv
  rw [hD, weakFDeriv_smulRightBaseW1pL, prev_smulRightBaseW1pL, hg, hv,
    smulRightGradientL_apply, ContinuousLinearMap.toSpanSingleton_apply, map_smul]

/-- **Scalar mode projection.** If `ℓ : H →L[ℝ] ℝ` satisfies `ℓ (A x) = λ * ℓ (ι x)` for all
`x ∈ D` (for example when `H` is a Hilbert space, `A` is `ι`-symmetric, and `ℓ = innerSL ℝ (ι a)`
for an eigenvector `A a = λ • ι a`), projecting `u` along `ℓ` via `TauCeti.WeakDerivStep.toW1pL`
turns `domainTrajectoryOperator ι A u` into the scalar `W^{1,p}` expression `u_ℓ' + λ u_ℓ`. -/
theorem compLpL_domainTrajectoryOperator_ae (ι A : D →L[ℝ] H) (ℓ : H →L[ℝ] ℝ) {lam : ℝ}
    (hℓ : ∀ x : D, ℓ (A x) = lam * ℓ (ι x))
    (u : WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega))) :
    ℓ.compLpL p (mu.restrict Omega) (domainTrajectoryOperator ι A u) =ᵐ[mu.restrict Omega]
      fun s ↦ ⟪W1p.gradient (toW1pL (ι.compLpL p (mu.restrict Omega)) ℓ u) s, (1 : ℝ)⟫_ℝ +
        lam * W1p.value (toW1pL (ι.compLpL p (mu.restrict Omega)) ℓ u) s := by
  let base := ι.compLpL p (mu.restrict Omega)
  filter_upwards [ℓ.coeFn_compLpL (domainTrajectoryOperator ι A u),
    domainTrajectoryOperator_apply_ae ι A u,
    inner_gradient_toW1pL_ae base ℓ u,
    ℓ.coeFn_compLpL (base (prev base u)),
    ι.coeFn_compLpL (prev base u)] with s h1 h2 hgrad hval hι
  rw [h1, h2, map_add, hℓ, value_toW1pL, hval, hι, hgrad 1]

end Modes

/-! ### Whole-line energy orthogonality and invertibility -/

section Symmetric

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {ι A : D →L[ℝ] H}

/-- Pairing a vector `v ∈ L²(ℝ, H)` against `domainTrajectoryOperator ι e (smulRightBaseW1pL ι
(e.symm h) φ)` extracts the weak-derivative test identity for `ι ∘ e.symm ∘ v`. -/
private theorem inner_domainTrajectoryOperator_ofTestFunction_eq
    (e : D ≃L[ℝ] H) (hSymm : ∀ x y : D, ⟪e x, ι y⟫_ℝ = ⟪ι x, e y⟫_ℝ)
    (v : Lp H 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) (h : H) (φ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    ⟪domainTrajectoryOperator ι (e : D →L[ℝ] H)
        (smulRightBaseW1pL ι (e.symm h) (W1p.ofTestFunctionₗ volume ⊤ 2 φ)), v⟫_ℝ =
      ⟪h, (∫ s, lineDeriv ℝ (φ : ℝ → ℝ) s 1 •
            (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
              ((e.symm : H →L[ℝ] D).compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) v)) s) +
          ∫ s, (φ : ℝ → ℝ) s • v s⟫_ℝ := by
  let μ := (volume : Measure ℝ).restrict ((⊤ : Opens ℝ) : Set ℝ)
  let z := ι.compLpL 2 μ ((e.symm : H →L[ℝ] D).compLpL 2 μ v)
  have hsymm' (x y : H) : ⟪ι (e.symm x), y⟫_ℝ = ⟪x, ι (e.symm y)⟫_ℝ := by
    calc ⟪ι (e.symm x), y⟫_ℝ = ⟪ι (e.symm x), e (e.symm y)⟫_ℝ := by rw [e.apply_symm_apply]
      _ = ⟪e (e.symm x), ι (e.symm y)⟫_ℝ := (hSymm _ _).symm
      _ = ⟪x, ι (e.symm y)⟫_ℝ := by rw [e.apply_symm_apply]
  have hi1 := integrable_lineDeriv_smul_of_locallyIntegrableOn
    (Lp.locallyIntegrableOn z (by norm_num)) φ 1
  have hi2 := φ.integrable_smul (Lp.locallyIntegrableOn v (by norm_num))
  rw [inner_add_right, ← integral_inner hi1, ← integral_inner hi2,
    ← integral_add (hi1.const_inner h) (hi2.const_inner h), L2.inner_def]
  refine (integral_congr_ae
    (g := fun s ↦ ⟪h, lineDeriv ℝ (φ : ℝ → ℝ) s 1 • z s⟫_ℝ + ⟪h, (φ : ℝ → ℝ) s • v s⟫_ℝ)
    ?_).trans setIntegral_univ
  let w := W1p.ofTestFunctionₗ volume ⊤ 2 φ
  filter_upwards [domainTrajectoryOperator_smulRightBaseW1pL_ae ι (e : D →L[ℝ] H) (e.symm h) w,
    testFunctionLp_apply_ae (mu := volume) 2 φ,
    gradientTestFunctionLp_apply_ae (mu := volume) 2 φ,
    ι.coeFn_compLpL ((e.symm : H →L[ℝ] D).compLpL 2 μ v),
    (e.symm : H →L[ℝ] D).coeFn_compLpL v] with s hD hval hgrad hι he
  have hz : z s = ι (e.symm (v s)) := by rw [hι, he, ContinuousLinearEquiv.coe_coe]
  rw [hD]
  simp only [w, W1p.value_ofTestFunctionₗ, W1p.gradient_ofTestFunctionₗ]
  simp [hz, hval, hgrad, gradient_eq_deriv', inner_add_left, inner_smul_left, inner_smul_right,
    hsymm']

variable [CompleteSpace D]

/-- **Whole-line `L²` orthogonality.** When `A` is `ι`-symmetric (`⟪A x, ι y⟫ = ⟪ι x, A y⟫`),
`(ι ∘ u)'` and `A ∘ u` are orthogonal in `L²(ℝ, H)` for every `u` in the common-domain Sobolev
space on the line. -/
theorem inner_weakFDeriv_apply_one_compLpL_eq_zero
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (u : WeakDerivStep volume ⊤ 2
      (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    ⟪(ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL 2
        (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
        (weakFDeriv (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u),
      A.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
        (prev (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u)⟫_ℝ = 0 := by
  let μ := (volume : Measure ℝ).restrict ((⊤ : Opens ℝ) : Set ℝ)
  let base := ι.compLpL 2 μ
  let L : H →L[ℝ] StrongDual ℝ D :=
    ((ContinuousLinearMap.compL ℝ D H ℝ).flip A).comp (innerSL ℝ)
  let B : D →L[ℝ] D →L[ℝ] ℝ := L.comp ι
  have hB : B.flip = B := by
    ext x y
    simp only [ContinuousLinearMap.flip_apply, B, L, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compL_apply, innerSL_apply_apply]
    rw [real_inner_comm, hSymm x y]
  have hx : MemLp ⇑(prev base u) 2 μ := Lp.memLp (prev base u)
  let d : ℝ → H := fun s ↦ weakFDeriv base u s 1
  have hd : MemLp d 2 μ :=
    (Lp.memLp (weakFDeriv base u)).continuousLinearMap_comp (ContinuousLinearMap.apply ℝ H 1)
  have hLd : MemLp (fun s ↦ L (d s)) 2 μ := hd.continuousLinearMap_comp L
  have hwB : HasWeakLineDerivOn volume ⊤ (fun s ↦ B (prev base u s)) (fun s ↦ L (d s)) 1 :=
    (((hasWeakFDerivOn_base_prev base u).hasWeakLineDerivOn 1).clm_comp L).congr_ae
      ((ι.coeFn_compLpL (prev base u)).mono fun s hs ↦ by simp [B, base, hs])
  have hprod := HasWeakLineDerivOn.bilin_self hB hwB hx hLd
  have hint0 : Integrable (fun s ↦ B (prev base u s) (prev base u s)) volume :=
    (memLp_one_iff_integrable.1 (B.memLp_of_bilin 1 hx hx)).mono_measure (by simp [μ])
  have hint1 : Integrable (fun s ↦ 2 * L (d s) (prev base u s)) volume :=
    ((memLp_one_iff_integrable.1
      ((ContinuousLinearMap.id ℝ (StrongDual ℝ D)).memLp_of_bilin 1 hLd hx)).const_mul 2)
      |>.mono_measure (by simp [μ])
  have hzero := hprod.integral_eq_zero_of_integrable hint0 hint1
  rw [MeasureTheory.integral_const_mul] at hzero
  have hint_eq : ⟪(ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL 2 μ (weakFDeriv base u),
      A.compLpL 2 μ (prev base u)⟫_ℝ = ∫ s, L (d s) (prev base u s) := by
    rw [L2.inner_def]
    refine (integral_congr_ae (g := fun s ↦ L (d s) (prev base u s)) ?_).trans (by simp [μ])
    filter_upwards [(ContinuousLinearMap.apply ℝ H (1 : ℝ)).coeFn_compLpL (weakFDeriv base u),
      A.coeFn_compLpL (prev base u)] with s hs1 hs2
    rw [hs1, hs2]
    simp [L, d]
  rw [hint_eq]
  linarith

/-- **The Pythagorean identity for `∂s ∘ ι + A`.** When `A` is `ι`-symmetric,
`‖(∂s ∘ ι + A) u‖² = ‖(ι ∘ u)'‖² + ‖A ∘ u‖²` on `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)`. -/
theorem norm_domainTrajectoryOperator_sq
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (u : WeakDerivStep volume ⊤ 2
      (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    ‖domainTrajectoryOperator ι A u‖ ^ 2 =
      ‖weakFDeriv (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u‖ ^ 2 +
        ‖A.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
          (prev (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u)‖ ^ 2 := by
  rw [domainTrajectoryOperator_apply, norm_add_sq_real,
    inner_weakFDeriv_apply_one_compLpL_eq_zero hSymm u, mul_zero, add_zero,
    ContinuousLinearMap.norm_apply_one_compLpL]

/-- The `L²` norm of `(ι ∘ u)'` is bounded by `‖(∂s ∘ ι + A) u‖`. -/
theorem norm_weakFDeriv_le_norm_domainTrajectoryOperator
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (u : WeakDerivStep volume ⊤ 2
      (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    ‖weakFDeriv (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u‖ ≤
      ‖domainTrajectoryOperator ι A u‖ := by
  refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
  rw [norm_domainTrajectoryOperator_sq hSymm u]
  linarith [sq_nonneg ‖A.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) (prev _ u)‖]

/-- The `L²` norm of `A ∘ u` is bounded by `‖(∂s ∘ ι + A) u‖`. -/
theorem norm_compLpL_prev_le_norm_domainTrajectoryOperator
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (u : WeakDerivStep volume ⊤ 2
      (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    ‖A.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
        (prev (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u)‖ ≤
      ‖domainTrajectoryOperator ι A u‖ := by
  refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
  rw [norm_domainTrajectoryOperator_sq hSymm u]
  linarith [sq_nonneg ‖weakFDeriv (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u‖]

/-- **Spectral-gap `L²` bound.** If `A` is `ι`-symmetric and satisfies `c ‖ι x‖ ≤ ‖A x‖` (`c > 0`),
then `‖ι ∘ u‖_{L²} ≤ c⁻¹ ‖(∂s ∘ ι + A) u‖_{L²}`. -/
theorem norm_compLpL_le_inv_mul_norm_domainTrajectoryOperator
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ x : D, c * ‖ι x‖ ≤ ‖A x‖)
    (u : WeakDerivStep volume ⊤ 2
      (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    ‖ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
        (prev (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u)‖ ≤
      c⁻¹ * ‖domainTrajectoryOperator ι A u‖ := by
  let μ := (volume : Measure ℝ).restrict ((⊤ : Opens ℝ) : Set ℝ)
  have h1 : c * ‖ι.compLpL 2 μ (prev (ι.compLpL 2 μ) u)‖ ≤
      ‖A.compLpL 2 μ (prev (ι.compLpL 2 μ) u)‖ := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
    rw [mul_pow, ← Lp.integral_norm_sq_eq_norm_sq, ← Lp.integral_norm_sq_eq_norm_sq,
      ← MeasureTheory.integral_const_mul]
    refine integral_mono_ae (((Lp.memLp _).integrable_norm_pow (by norm_num)).const_mul _)
      ((Lp.memLp _).integrable_norm_pow (by norm_num)) ?_
    filter_upwards [ι.coeFn_compLpL (prev (ι.compLpL 2 μ) u),
      A.coeFn_compLpL (prev (ι.compLpL 2 μ) u)] with s hι hA
    rw [hι, hA, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (hgap _) 2
  exact (le_inv_mul_iff₀ hc).2
    (h1.trans (norm_compLpL_prev_le_norm_domainTrajectoryOperator hSymm u))

/-- **Injectivity without invertibility of `A`.** When `ι` is injective and `A` is `ι`-symmetric,
`∂s ∘ ι + A` is injective on `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` even if `A.ker ≠ ⊥`. -/
theorem injective_domainTrajectoryOperator_of_symmetric (hι : Function.Injective ι)
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) :
    Function.Injective
      (domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A) := by
  refine (injective_iff_map_eq_zero _).2 fun u hu ↦ ?_
  have hw0 : weakFDeriv _ u = 0 := norm_le_zero_iff.mp <| by
    simpa [hu] using norm_weakFDeriv_le_norm_domainTrajectoryOperator hSymm u
  have hv_zero : toIdL (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u = 0 :=
    eq_zero_of_weakFDeriv_eq_zero (p := 2) ENNReal.ofNat_ne_top
      (by rw [weakFDeriv_toIdL, hw0])
  have hprev_v : ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) (prev _ u) = 0 := by
    have h0 := congrArg (prev _) hv_zero
    rwa [prev_toIdL, prev_zero] at h0
  apply ext
  rw [prev_zero]
  apply Lp.ext
  filter_upwards [ι.coeFn_compLpL (prev _ u), hprev_v ▸ Lp.coeFn_zero H 2 _,
    Lp.coeFn_zero D 2 _] with s hs h0 hd0
  rw [hd0, Pi.zero_apply]
  exact hι (by rw [← hs, h0, Pi.zero_apply, map_zero])

/-- **Coercive graph-norm estimate.** When `A` is `ι`-symmetric and invertible,
`‖u‖ ≤ √(1 + ‖A.inverse‖²) ‖(∂s ∘ ι + A) u‖` for every `u` in `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)`. -/
theorem norm_le_sqrt_one_add_sq_mul_norm_domainTrajectoryOperator
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hA : A.IsInvertible)
    (u : WeakDerivStep volume ⊤ 2
      (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    ‖u‖ ≤ √(1 + ‖A.inverse‖ ^ 2) * ‖domainTrajectoryOperator ι A u‖ := by
  obtain ⟨e, rfl⟩ := hA
  rw [ContinuousLinearMap.inverse_equiv]
  let μ := (volume : Measure ℝ).restrict ((⊤ : Opens ℝ) : Set ℝ)
  let base := ι.compLpL 2 μ
  have hprev :
      ‖prev base u‖ ≤ ‖(e.symm : H →L[ℝ] D)‖ * ‖(e : D →L[ℝ] H).compLpL 2 μ (prev base u)‖ := by
    have hcomp : (e.symm : H →L[ℝ] D).comp (e : D →L[ℝ] H) = .id ℝ D := by
      ext
      simp
    have hid : (e.symm : H →L[ℝ] D).compLpL 2 μ ((e : D →L[ℝ] H).compLpL 2 μ (prev base u)) =
        prev base u := by
      rw [ContinuousLinearMap.compLpL_compLpL, hcomp, ContinuousLinearMap.id_compLpL,
        ContinuousLinearMap.id_apply]
    calc ‖prev base u‖
        = ‖(e.symm : H →L[ℝ] D).compLpL 2 μ ((e : D →L[ℝ] H).compLpL 2 μ (prev base u))‖ := by
          rw [hid]
      _ ≤ ‖(e.symm : H →L[ℝ] D).compLpL 2 μ‖ * ‖(e : D →L[ℝ] H).compLpL 2 μ (prev base u)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖(e.symm : H →L[ℝ] D)‖ * ‖(e : D →L[ℝ] H).compLpL 2 μ (prev base u)‖ := by
          gcongr
          exact (e.symm : H →L[ℝ] D).norm_compLpL_le
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [mul_pow, Real.sq_sqrt (by positivity), norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq,
    norm_domainTrajectoryOperator_sq hSymm u]
  have hsq : ‖prev base u‖ ^ 2 ≤
      ‖(e.symm : H →L[ℝ] D)‖ ^ 2 * ‖(e : D →L[ℝ] H).compLpL 2 μ (prev base u)‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hprev 2
  nlinarith [sq_nonneg ‖weakFDeriv base u‖, sq_nonneg ‖(e.symm : H →L[ℝ] D)‖,
    sq_nonneg ‖(e : D →L[ℝ] H).compLpL 2 μ (prev base u)‖]

/-- Any `L²` path orthogonal to the range of `domainTrajectoryOperator ι A` vanishes when `A` is
`ι`-symmetric and invertible. -/
private theorem eq_zero_of_mem_orthogonal_range_domainTrajectoryOperator
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hA : A.IsInvertible)
    {v : Lp H 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hv : v ∈ (domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).rangeᗮ) :
    v = 0 := by
  obtain ⟨e, rfl⟩ := hA
  let μ := (volume : Measure ℝ).restrict ((⊤ : Opens ℝ) : Set ℝ)
  let x := (e.symm : H →L[ℝ] D).compLpL 2 μ v
  have hweak : HasWeakLineDerivOn volume ⊤ (ι.compLpL 2 μ x) (fun s ↦ v s) 1 := by
    rw [hasWeakLineDerivOn_iff_testFunction]
    refine ⟨inferInstance, Lp.locallyIntegrableOn _ (by norm_num),
      Lp.locallyIntegrableOn v (by norm_num), fun φ ↦ add_eq_zero_iff_eq_neg.mp ?_⟩
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [← inner_domainTrajectoryOperator_ofTestFunction_eq e hSymm v _ φ, real_inner_comm]
    exact (Submodule.mem_orthogonal' _ _).mp hv _ ⟨_, rfl⟩
  have hweak' : HasWeakLineDerivOn volume ⊤ (ι.compLpL 2 μ x)
      (fun s ↦ ((2 : ℝ) • v : Lp H 2 μ) s - (e : D →L[ℝ] H) (x s)) 1 := by
    refine hweak.congr_ae_deriv ?_
    filter_upwards [Lp.coeFn_smul (2 : ℝ) v,
      (e.symm : H →L[ℝ] D).coeFn_compLpL v] with s hsmul hs
    rw [hsmul, Pi.smul_apply, two_smul, hs, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_coe, e.apply_symm_apply, add_sub_cancel_right]
  obtain ⟨w, hwx, hDw⟩ := exists_prev_eq_and_domainTrajectoryOperator_eq_of_hasWeakLineDerivOn
    ι (e : D →L[ℝ] H) (f := (2 : ℝ) • v) hweak'
  have hcomp : (e : D →L[ℝ] H).comp (e.symm : H →L[ℝ] D) = .id ℝ H := by
    ext
    simp
  have hAw : (e : D →L[ℝ] H).compLpL 2 μ (prev _ w) = v := by
    rw [hwx, ContinuousLinearMap.compLpL_compLpL, hcomp, ContinuousLinearMap.id_compLpL,
      ContinuousLinearMap.id_apply]
  have hw' : (ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL 2 μ (weakFDeriv _ w) = v := by
    have h1 := domainTrajectoryOperator_apply ι (e : D →L[ℝ] H) w
    rw [hDw, hAw, two_smul] at h1
    exact add_right_cancel h1.symm
  have h0 := inner_weakFDeriv_apply_one_compLpL_eq_zero hSymm w
  rw [hw', hAw, inner_self_eq_zero] at h0
  exact h0

/-- **Bijectivity of `∂s ∘ ι + A`.** When `A` is `ι`-symmetric and invertible, `∂s ∘ ι + A` is a
bijection from `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` onto `L²(ℝ, H)`. -/
theorem bijective_domainTrajectoryOperator
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hA : A.IsInvertible) :
    Function.Bijective
      (domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A) := by
  set T := domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A
  let C : NNReal := ⟨√(1 + ‖A.inverse‖ ^ 2), Real.sqrt_nonneg _⟩
  have hanti : AntilipschitzWith C T :=
    T.antilipschitz_of_bound (norm_le_sqrt_one_add_sq_mul_norm_domainTrajectoryOperator hSymm hA)
  have hclosed : IsClosed (T.range : Set (Lp H 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :=
    (hanti.isClosedEmbedding T.uniformContinuous).isClosed_range
  have := hclosed.completeSpace_coe
  refine ⟨hanti.injective, LinearMap.range_eq_top.mp ?_⟩
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
  intro v hv
  exact eq_zero_of_mem_orthogonal_range_domainTrajectoryOperator hSymm hA hv

/-- **Invertibility of `∂s ∘ ι + A`.** When `A` is `ι`-symmetric and invertible, `∂s ∘ ι + A` is a
continuous linear isomorphism `L²(ℝ, D) ∩ W^{1,2}(ℝ, H) →L[ℝ] L²(ℝ, H)`. -/
theorem isInvertible_domainTrajectoryOperator
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hA : A.IsInvertible) :
    (domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).IsInvertible :=
  ContinuousLinearMap.isInvertible_of_surjective_of_forall_norm_le
    (bijective_domainTrajectoryOperator hSymm hA).2
    (norm_le_sqrt_one_add_sq_mul_norm_domainTrajectoryOperator hSymm hA)

/-- **Explicit inverse-norm bound.** When `A` is `ι`-symmetric and invertible, the inverse of
`∂s ∘ ι + A` has operator norm at most `√(1 + ‖A.inverse‖²)`. -/
theorem norm_inverse_domainTrajectoryOperator_le
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hA : A.IsInvertible) :
    ‖(domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).inverse‖ ≤
      √(1 + ‖A.inverse‖ ^ 2) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    (ContinuousLinearMap.norm_inverse_apply_le_of_forall_norm_le
      (bijective_domainTrajectoryOperator hSymm hA).2
      (norm_le_sqrt_one_add_sq_mul_norm_domainTrajectoryOperator hSymm hA))

/-- When `A` is `ι`-symmetric and invertible, `∂s ∘ ι + A` is Fredholm. -/
theorem isFredholm_domainTrajectoryOperator
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hA : A.IsInvertible) :
    (domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).IsFredholm :=
  (isInvertible_domainTrajectoryOperator hSymm hA).isFredholm

/-- When `A` is `ι`-symmetric and invertible, the Fredholm index of `∂s ∘ ι + A` is `0`. -/
theorem index_domainTrajectoryOperator
    (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hA : A.IsInvertible) :
    (domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).index = 0 :=
  ContinuousLinearMap.index_eq_zero_of_bijective _
    (bijective_domainTrajectoryOperator hSymm hA)

/-! ### Non-closed range when `A.ker ≠ ⊥` -/

/-- **A nontrivial kernel in `A` destroys closed range of `∂s ∘ ι + A`.** When `ι` is injective,
`A` is `ι`-symmetric, and `A.ker ≠ ⊥`, the range of `domainTrajectoryOperator ι A` on
`L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` is not closed in `L²(ℝ, H)`. -/
theorem not_isClosed_range_domainTrajectoryOperator_of_ker_ne_bot
    (hι : Function.Injective ι) (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (hker : A.ker ≠ ⊥) :
    ¬ IsClosed ((domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).range :
      Set (Lp H 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) := by
  intro hclosed
  obtain ⟨a, hAa, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hAa
  set T := domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A
  obtain ⟨K, hK⟩ := T.antilipschitz_of_injective_of_isClosed_range
    (injective_domainTrajectoryOperator_of_symmetric hι hSymm) hclosed
  obtain ⟨C, hplat⟩ := exists_forall_contDiff_plateau
  have ha_pos : 0 < ‖a‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.2 ha)
  let r : ℝ := max 0 (((K : ℝ) ^ 2 * C * ‖ι a‖ ^ 2) / (2 * ‖a‖ ^ 2) + 1)
  have hr : 0 ≤ r := le_max_left _ _
  have hr_gt : ((K : ℝ) ^ 2 * C * ‖ι a‖ ^ 2) / (2 * ‖a‖ ^ 2) < r :=
    lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
  obtain ⟨ψ, hψ, hψsupp, hψ2, hψd⟩ := hplat 0 hr
  have hψc : HasCompactSupport ψ :=
    (isCompact_closedBall 0 (r + 1)).of_isClosed_subset (isClosed_tsupport ψ) hψsupp
  let φ : 𝓓((⊤ : Opens ℝ), ℝ) := ⟨ψ, hψ, hψc, subset_univ _⟩
  let u := smulRightBaseW1pL ι a (W1p.ofTestFunctionₗ volume ⊤ 2 φ)
  have hprev_sq : ‖prev _ u‖ ^ 2 = (∫ s, ψ s ^ 2) * ‖a‖ ^ 2 := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    have hae : (fun s ↦ ‖prev _ u s‖ ^ 2) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
        fun s ↦ ψ s ^ 2 * ‖a‖ ^ 2 := by
      filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ a).coeFn_compLpL
          (testFunctionLp (mu := volume) 2 φ),
        testFunctionLp_apply_ae (mu := volume) 2 φ] with s h1 h2
      simp only [u, φ, prev_smulRightBaseW1pL, W1p.value_ofTestFunctionₗ, h1, h2,
        TestFunction.coe_mk, ContinuousLinearMap.toSpanSingleton_apply, norm_smul,
        Real.norm_eq_abs, mul_pow, sq_abs]
    rw [integral_congr_ae hae, Opens.coe_top, Measure.restrict_univ,
      MeasureTheory.integral_mul_const]
  have hTu_sq : ‖T u‖ ^ 2 = (∫ s, deriv ψ s ^ 2) * ‖ι a‖ ^ 2 := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    have hae : (fun s ↦ ‖T u s‖ ^ 2) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
        fun s ↦ deriv ψ s ^ 2 * ‖ι a‖ ^ 2 := by
      filter_upwards [domainTrajectoryOperator_smulRightBaseW1pL_ae ι A a
          (W1p.ofTestFunctionₗ volume ⊤ 2 φ),
        gradientTestFunctionLp_apply_ae (mu := volume) 2 φ] with s h1 h2
      simp only [T, u, h1, hAa, smul_zero, add_zero, W1p.gradient_ofTestFunctionₗ, h2,
        gradient_eq_deriv', RCLike.inner_apply, RCLike.conj_to_real, one_mul,
        φ, TestFunction.coe_mk, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [integral_congr_ae hae, Opens.coe_top, Measure.restrict_univ,
      MeasureTheory.integral_mul_const]
  have hle : ‖prev _ u‖ ≤ (K : ℝ) * ‖T u‖ :=
    (norm_prev_le _ u).trans (hK.le_mul_norm (map_zero T) u)
  have hsq : (∫ s, ψ s ^ 2) * ‖a‖ ^ 2 ≤ (K : ℝ) ^ 2 * ((∫ s, deriv ψ s ^ 2) * ‖ι a‖ ^ 2) := by
    rw [← hprev_sq, ← hTu_sq, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hlo : 2 * r * ‖a‖ ^ 2 ≤ (∫ s, ψ s ^ 2) * ‖a‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hψ2 (sq_nonneg _)
  have hhi : (K : ℝ) ^ 2 * ((∫ s, deriv ψ s ^ 2) * ‖ι a‖ ^ 2) ≤
      (K : ℝ) ^ 2 * C * ‖ι a‖ ^ 2 := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hψd (sq_nonneg _)) (sq_nonneg _)
  have hlt : (K : ℝ) ^ 2 * C * ‖ι a‖ ^ 2 < 2 * r * ‖a‖ ^ 2 := by
    linarith [(div_lt_iff₀ (mul_pos zero_lt_two ha_pos)).mp hr_gt,
      show r * (2 * ‖a‖ ^ 2) = 2 * r * ‖a‖ ^ 2 by ring]
  exact hlt.not_ge (hlo.trans (hsq.trans hhi))

/-- When `ι` is injective and `A` is `ι`-symmetric and Fredholm of index zero, the range of
`domainTrajectoryOperator ι A` on `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` is closed if and only if `A` is
invertible. -/
theorem isClosed_range_domainTrajectoryOperator_iff
    (hι : Function.Injective ι) (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (hAF : A.IsFredholm) (hAi : A.index = 0) :
    IsClosed ((domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).range :
      Set (Lp H 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ↔ A.IsInvertible := by
  refine ⟨fun hclosed ↦ ?_,
    fun hA ↦ (isInvertible_domainTrajectoryOperator hSymm hA).isFredholm.isClosed_range⟩
  refine hAF.isInvertible_of_injective_of_index_eq_zero (LinearMap.ker_eq_bot.mp ?_) hAi
  by_contra hker
  exact not_isClosed_range_domainTrajectoryOperator_of_ker_ne_bot hι hSymm hker hclosed

/-- When `ι` is injective and `A` is `ι`-symmetric and Fredholm of index zero,
`domainTrajectoryOperator ι A` is Fredholm on `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` if and only if `A` is
invertible. -/
theorem isFredholm_domainTrajectoryOperator_iff
    (hι : Function.Injective ι) (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (hAF : A.IsFredholm) (hAi : A.index = 0) :
    (domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).IsFredholm ↔
      A.IsInvertible :=
  ⟨fun hF ↦ (isClosed_range_domainTrajectoryOperator_iff hι hSymm hAF hAi).mp hF.isClosed_range,
    isFredholm_domainTrajectoryOperator hSymm⟩

/-- When `ι` is injective and `A` is `ι`-symmetric and Fredholm of index zero,
`domainTrajectoryOperator ι A` is invertible on `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` if and only if `A` is
invertible. -/
theorem isInvertible_domainTrajectoryOperator_iff
    (hι : Function.Injective ι) (hSymm : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (hAF : A.IsFredholm) (hAi : A.index = 0) :
    (domainTrajectoryOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).IsInvertible ↔
      A.IsInvertible :=
  ⟨fun hT ↦ (isFredholm_domainTrajectoryOperator_iff hι hSymm hAF hAi).mp hT.isFredholm,
    isInvertible_domainTrajectoryOperator hSymm⟩

end Symmetric

end TauCeti.WeakDerivStep
