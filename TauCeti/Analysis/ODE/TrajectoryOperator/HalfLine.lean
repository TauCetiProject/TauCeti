/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.EnergyEstimate.Index
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.ODE.Caratheodory
import TauCeti.Analysis.ODE.DysonSeries
import TauCeti.Analysis.ODE.ScalarLinear
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Half-line solutions and the surjectivity of the trajectory operator

Let `A : ℝ → End(E)` be a continuous family of operators on a finite-dimensional real inner product
space `E`, and consider the linear equation `v' + A(s) v = 0` on the whole line. Its solutions are
determined by their values at time `0`, and three subspaces of `E` record their decay:

* `TauCeti.squareIntegrableSolutionsOn A (Ioi 0)`, the initial values of the solutions that are
  square integrable on `(0, ∞)`, the *stable* solutions;
* `TauCeti.squareIntegrableSolutionsOn A (Iio 0)`, those square integrable on `(-∞, 0)`, the
  *unstable* solutions;
* `TauCeti.squareIntegrableSolutions A`, those square integrable on the whole line, which is the
  intersection of the first two (`TauCeti.squareIntegrableSolutionsOn_Iio_inf_Ioi`) and models the
  kernel of the trajectory operator `D_A u = u' + A u` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)`.

For the linearization `A(s) = Hess f(γ s)` along a gradient trajectory `γ` from `p` to `q`,
classically the stable and unstable solutions are the tangent spaces at `γ 0` of the stable set of
`q` and of the unstable set of `p`; that identification is not formalized here.

For a continuous family of symmetric operators with invertible limits `A±` at `±∞` this file
computes their dimensions and identifies the cokernel of `D_A` with the failure of the stable and
unstable solutions to span `E`:

* the stable solutions have the dimension of the positive spectral subspace of `A⁺`
  (`TauCeti.finrank_squareIntegrableSolutionsOn_Ioi`), and the unstable ones that of the negative
  spectral subspace of `A⁻` (`TauCeti.finrank_squareIntegrableSolutionsOn_Iio`);
* the square-integrable solutions of the adjoint equation `w' = A w`, which model the cokernel of
  `D_A`, are the orthogonal complement of the sum of the stable and unstable solutions
  (`TauCeti.squareIntegrableSolutions_neg_eq_orthogonal_sup`);
* hence `D_A` is surjective exactly when the stable and unstable solutions span `E`
  (`TauCeti.WeakDerivStep.surjective_trajectoryOperator_iff_sup_eq_top`).

For the linearized gradient flow the last statement is the linear half of the classical fact that
the linearized operator is onto exactly when the unstable and stable sets meet transversally along
`γ`, which compares the Fredholm description of the spaces of gradient trajectories with their
description as intersections of unstable and stable sets.

## Proofs

If `v` solves `v' = -A v` and `w` solves the adjoint equation `w' = A w`, then `⟪v, w⟫` is
constant, by symmetry of `A`. When both are square integrable on a half-line this constant is
integrable there, hence zero; so the adjoint solutions square integrable on a half-line are
orthogonal to the solutions square integrable on the same half-line
(`TauCeti.squareIntegrableSolutionsOn_neg_le_orthogonal`). This gives one inclusion of the
cokernel identification, and the other follows by counting dimensions with the index formula
`TauCeti.WeakDerivStep.index_trajectoryOperator_eq_finrank_pointSpectralSubspace_sub_finrank`.

The dimension of the stable solutions is itself computed with the index formula. The stable
solutions only depend on `A` on `[0, ∞)`
(`TauCeti.squareIntegrableSolutionsOn_Ioi_congr`), so `A` may be replaced on `(-∞, 0]` by a
family equal to `-id` before time `-1`. For the new family every solution is square integrable on
`(-∞, 0)` and no nonzero adjoint solution is, so its trajectory operator has the stable
solutions of `A` as kernel, no cokernel, and index the dimension of the positive spectral subspace
of `A⁺`. The
unstable solutions of `A` are the stable solutions of the reflected family `s ↦ -A(-s)`
(`TauCeti.squareIntegrableSolutionsOn_Iio_eq_Ioi`).

## References

* M. Schwarz, *Morse Homology*, Birkhäuser, 1993, Chapter 2 (the kernel and cokernel of the
  linearized trajectory operator through decaying solutions, and transversality).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic Geometry and Topology*, IAS/Park City
  Math. Ser. **7**, 1999, Lecture 2 (the linearized operator is onto exactly when the unstable and
  stable manifolds intersect transversally).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal Topology InnerProductSpace

namespace TauCeti

section Solutions

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {A B : ℝ → F →L[ℝ] F}
  {s t : Set ℝ}

/-- The initial values at time `0` of the solutions `v : ℝ → F` of the linear equation
`v' + A(τ) v = 0` on the whole line that are square integrable on the set `s` of times. For
`s = Ioi 0` these are the stable solutions, for `s = Iio 0` the unstable ones, and for
`s = univ` the square-integrable solutions `TauCeti.squareIntegrableSolutions A`. -/
def squareIntegrableSolutionsOn (A : ℝ → F →L[ℝ] F) (s : Set ℝ) : Submodule ℝ F where
  carrier := {x | ∃ v : ℝ → F, v 0 = x ∧ (∀ τ, HasDerivAt v (-A τ (v τ)) τ) ∧
    MemLp v 2 (volume.restrict s)}
  zero_mem' := ⟨0, rfl, fun τ ↦ by simp, MemLp.zero⟩
  add_mem' := by
    rintro _ _ ⟨v, rfl, hv, hv2⟩ ⟨w, rfl, hw, hw2⟩
    exact ⟨v + w, rfl, fun τ ↦ by simpa [add_comm] using (hv τ).add (hw τ), hv2.add hw2⟩
  smul_mem' := by
    rintro c _ ⟨v, rfl, hv, hv2⟩
    exact ⟨c • v, rfl, fun τ ↦ by simpa using (hv τ).const_smul c, hv2.const_smul c⟩

/-- A vector lies in `TauCeti.squareIntegrableSolutionsOn A s` when it is the value at time `0` of
a solution of `v' + A v = 0` that is square integrable on `s`. -/
theorem mem_squareIntegrableSolutionsOn {x : F} :
    x ∈ squareIntegrableSolutionsOn A s ↔
      ∃ v : ℝ → F, v 0 = x ∧ (∀ τ, HasDerivAt v (-A τ (v τ)) τ) ∧
        MemLp v 2 (volume.restrict s) :=
  Iff.rfl

/-- Square integrability on a larger set of times is a stronger condition. -/
theorem squareIntegrableSolutionsOn_antitone (A : ℝ → F →L[ℝ] F) :
    Antitone (squareIntegrableSolutionsOn A) := fun _ _ hst _ ⟨v, hv0, hv, hv2⟩ ↦
  ⟨v, hv0, hv, hv2.mono_measure (Measure.restrict_mono hst le_rfl)⟩

/-- The solutions square integrable on the whole line are `TauCeti.squareIntegrableSolutions A`. -/
@[simp]
theorem squareIntegrableSolutionsOn_univ (A : ℝ → F →L[ℝ] F) :
    squareIntegrableSolutionsOn A univ = squareIntegrableSolutions A := by
  ext x
  simp [mem_squareIntegrableSolutionsOn, mem_squareIntegrableSolutions]

/-- A solution square integrable on the whole line is square integrable on every set of times. -/
theorem squareIntegrableSolutions_le_squareIntegrableSolutionsOn (A : ℝ → F →L[ℝ] F)
    (s : Set ℝ) : squareIntegrableSolutions A ≤ squareIntegrableSolutionsOn A s :=
  squareIntegrableSolutionsOn_univ A ▸ squareIntegrableSolutionsOn_antitone A (subset_univ s)

/-- **A solution square integrable on both half-lines is square integrable.** Two solutions with
the same value at time `0` coincide, so the solutions square integrable on `(-∞, 0)` and on
`(0, ∞)` are those square integrable on the whole line. -/
theorem squareIntegrableSolutionsOn_Iio_inf_Ioi (hA : Continuous A) :
    squareIntegrableSolutionsOn A (Iio 0) ⊓ squareIntegrableSolutionsOn A (Ioi 0) =
      squareIntegrableSolutions A := by
  refine le_antisymm (fun x hx ↦ ?_)
    (le_inf (squareIntegrableSolutions_le_squareIntegrableSolutionsOn A _)
      (squareIntegrableSolutions_le_squareIntegrableSolutionsOn A _))
  obtain ⟨⟨v, hv0, hv, hv2⟩, ⟨w, hw0, hw, hw2⟩⟩ := Submodule.mem_inf.1 hx
  have hvw : v = w := hA.neg.eq_of_hasDerivAt_clm_apply (fun τ ↦ by simpa using hv τ)
    (fun τ ↦ by simpa using hw τ) (t₀ := 0) (hv0.trans hw0.symm)
  subst hvw
  have hcont : Continuous v := continuous_iff_continuousAt.2 fun τ ↦ (hv τ).continuousAt
  refine mem_squareIntegrableSolutions.2 ⟨v, hv0, hv, ?_⟩
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable] at hv2 hw2 ⊢
  rw [← integrableOn_univ, ← Iio_union_Ici (a := (0 : ℝ)), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨hv2, hw2⟩

/-- **The stable solutions only depend on the equation in forward time.** If `A` and `B` agree on
`[0, ∞)`, then the solutions of `v' + A v = 0` and of `v' + B v = 0` that are square integrable on
`(0, ∞)` have the same initial values. -/
theorem squareIntegrableSolutionsOn_Ioi_congr [CompleteSpace F] (hA : Continuous A)
    (hB : Continuous B) (hAB : ∀ τ, 0 ≤ τ → A τ = B τ) :
    squareIntegrableSolutionsOn A (Ioi 0) = squareIntegrableSolutionsOn B (Ioi 0) := by
  -- The inclusion for any two such families, applied in both orders.
  have key {A B : ℝ → F →L[ℝ] F} (hB : Continuous B) (hAB : ∀ τ, 0 ≤ τ → A τ = B τ) :
      squareIntegrableSolutionsOn A (Ioi 0) ≤ squareIntegrableSolutionsOn B (Ioi 0) := by
    rintro _ ⟨v, rfl, hv, hv2⟩
    -- The solution of the second equation through `v 0` agrees with `v` on `[0, ∞)`.
    set w : ℝ → F := fun τ ↦ dysonSeriesLeft (-B) τ (v 0)
    have hw (τ : ℝ) : HasDerivAt w (-B τ (w τ)) τ := by
      simpa [w] using hasDerivAt_dysonSeriesLeft_apply hB.neg (v 0) τ
    have hvw : EqOn v w (Ici 0) := hB.neg.eqOn_Ici_of_hasDerivAt_clm_apply
      (fun τ hτ ↦ by simpa [← hAB τ hτ] using hv τ) (fun τ _ ↦ by simpa using hw τ)
      (by simp [w])
    refine ⟨w, by simp [w], hw, hv2.ae_eq ?_⟩
    exact (ae_restrict_mem measurableSet_Ioi).mono fun τ hτ ↦ hvw (mem_Ici.2 (le_of_lt hτ))
  exact le_antisymm (key hB hAB) (key hA fun τ hτ ↦ (hAB τ hτ).symm)

/-- Reflecting time turns solutions of `v' + A(τ) v = 0` square integrable on `t` into solutions
of `w' - A(-τ) w = 0` square integrable on the reflected set `s = -t`. -/
private theorem squareIntegrableSolutionsOn_le_reflect (hst : Neg.neg ⁻¹' t = s)
    (ht : MeasurableSet t) :
    squareIntegrableSolutionsOn A t ≤ squareIntegrableSolutionsOn (fun τ ↦ -A (-τ)) s := by
  rintro _ ⟨v, rfl, hv, hv2⟩
  refine ⟨fun τ ↦ v (-τ), by simp, fun τ ↦ ?_, ?_⟩
  · simpa [Function.comp_def] using (hv (-τ)).scomp τ (hasDerivAt_neg τ)
  · have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage ht
    rw [hst] at hmp
    exact hv2.comp_measurePreserving hmp

/-- **The unstable solutions are the stable solutions of the reflected equation.** The solutions
of `v' + A(τ) v = 0` that are square integrable on `(-∞, 0)` have the same initial values as the
solutions of `w' - A(-τ) w = 0` that are square integrable on `(0, ∞)`, through
`w(τ) = v(-τ)`. -/
theorem squareIntegrableSolutionsOn_Iio_eq_Ioi (A : ℝ → F →L[ℝ] F) :
    squareIntegrableSolutionsOn A (Iio 0) =
      squareIntegrableSolutionsOn (fun τ ↦ -A (-τ)) (Ioi 0) := by
  refine le_antisymm (squareIntegrableSolutionsOn_le_reflect (s := Ioi 0) (t := Iio 0)
    (by ext; simp) measurableSet_Iio) ?_
  have h := squareIntegrableSolutionsOn_le_reflect (A := fun τ ↦ -A (-τ)) (s := Iio 0)
    (t := Ioi 0) (by ext; simp) measurableSet_Ioi
  simpa using h

end Solutions

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {A : ℝ → E →L[ℝ] E}
  {s : Set ℝ}

/-- **Adjoint solutions decaying on a set are orthogonal to solutions decaying there.** For a
family of symmetric operators, if `v' = -A v` and `w' = A w`, then `⟪v, w⟫` is constant. When `v`
and `w` are square integrable on a set `s` of infinite measure, such as a half-line, this constant
is integrable on `s`, hence zero. So the solutions of the adjoint equation square integrable on
`s` are orthogonal to the solutions of `v' + A v = 0` square integrable on `s`. -/
theorem squareIntegrableSolutionsOn_neg_le_orthogonal
    (hsym : ∀ τ, (A τ).toLinearMap.IsSymmetric) (hs : volume s = ∞) :
    squareIntegrableSolutionsOn (-A) s ≤ (squareIntegrableSolutionsOn A s)ᗮ := by
  rintro _ ⟨w, rfl, hw, hw2⟩
  refine (Submodule.mem_orthogonal _ _).2 fun _ ⟨v, hv0, hv, hv2⟩ ↦ ?_
  subst hv0
  -- The pairing `⟪v, w⟫` has derivative `⟪-A v, w⟫ + ⟪v, A w⟫ = 0`, so it is constant.
  have hderiv (τ : ℝ) : HasDerivAt (fun τ ↦ ⟪v τ, w τ⟫_ℝ) 0 τ := by
    have h := (hv τ).inner ℝ (hw τ)
    rwa [Pi.neg_apply, neg_apply, neg_neg, inner_neg_left, (hsym τ).apply_clm,
      add_neg_cancel] at h
  have hconst (τ : ℝ) : ⟪v τ, w τ⟫_ℝ = ⟪v 0, w 0⟫_ℝ :=
    is_const_of_deriv_eq_zero (fun τ ↦ (hderiv τ).differentiableAt) (fun τ ↦ (hderiv τ).deriv)
      τ 0
  -- A product of two square-integrable functions is integrable, by Hölder's inequality.
  have hint : IntegrableOn (fun τ ↦ ⟪v τ, w τ⟫_ℝ) s :=
    memLp_one_iff_integrable.1 ((innerSL ℝ).memLp_of_bilin 1 hv2 hw2)
  simp_rw [hconst] at hint
  rw [integrableOn_const_iff, hs] at hint
  simpa using hint

end InnerProduct

/-! ### The dimensions of the stable and unstable solutions -/

section Dimension

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {A : ℝ → E →L[ℝ] E}

/-- The family `A` capped on the left: equal to `A` on `[0, ∞)` and to `-id` on `(-∞, -1]`,
interpolating by Mathlib's smooth transition function in between. -/
private def leftCap (A : ℝ → E →L[ℝ] E) (τ : ℝ) : E →L[ℝ] E :=
  Real.smoothTransition (-τ) • (-ContinuousLinearMap.id ℝ E) +
    (1 - Real.smoothTransition (-τ)) • A τ

private theorem leftCap_of_nonneg {τ : ℝ} (hτ : 0 ≤ τ) : leftCap A τ = A τ := by
  simp [leftCap, Real.smoothTransition.zero_of_nonpos (neg_nonpos.2 hτ)]

private theorem leftCap_of_le_neg_one {τ : ℝ} (hτ : τ ≤ -1) :
    leftCap A τ = -ContinuousLinearMap.id ℝ E := by
  simp [leftCap, Real.smoothTransition.one_of_one_le (le_neg_of_le_neg hτ)]

private theorem continuous_leftCap (hA : Continuous A) : Continuous (leftCap A) :=
  ((Real.smoothTransition.continuous.comp continuous_neg).smul continuous_const).add
    ((continuous_const.sub (Real.smoothTransition.continuous.comp continuous_neg)).smul hA)

private theorem isSymmetric_leftCap (hsym : ∀ τ, (A τ).toLinearMap.IsSymmetric) (τ : ℝ) :
    (leftCap A τ).toLinearMap.IsSymmetric := fun x y ↦ by
  simp only [leftCap, ContinuousLinearMap.coe_coe, add_apply, smul_apply, neg_apply,
    ContinuousLinearMap.id_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, inner_neg_left,
    inner_neg_right, (hsym τ).apply_clm, RCLike.conj_to_real]

private theorem tendsto_leftCap_atBot :
    Tendsto (leftCap A) atBot (𝓝 (-ContinuousLinearMap.id ℝ E)) :=
  tendsto_const_nhds.congr' <| (eventually_le_atBot (-1)).mono fun _ hτ ↦
    (leftCap_of_le_neg_one hτ).symm

private theorem tendsto_leftCap_atTop {Aplus : E →L[ℝ] E} (htop : Tendsto A atTop (𝓝 Aplus)) :
    Tendsto (leftCap A) atTop (𝓝 Aplus) :=
  htop.congr' <| (eventually_ge_atTop 0).mono fun _ hτ ↦ (leftCap_of_nonneg hτ).symm

variable [FiniteDimensional ℝ E]

/-- Every solution of `v' = -leftCap A v` is square integrable on `(-∞, 0)`: before time `-1` it
is `exp (τ + 1) v(-1)`. -/
private theorem squareIntegrableSolutionsOn_leftCap_Iio (hA : Continuous A) :
    squareIntegrableSolutionsOn (leftCap A) (Iio 0) = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  set v : ℝ → E := fun τ ↦ dysonSeriesLeft (-leftCap A) τ x
  have hv (τ : ℝ) : HasDerivAt v (-leftCap A τ (v τ)) τ := by
    simpa [v] using hasDerivAt_dysonSeriesLeft_apply (continuous_leftCap hA).neg x τ
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun τ ↦ (hv τ).continuousAt
  refine ⟨v, by simp [v], hv, ?_⟩
  rw [memLp_two_iff_integrable_sq_norm hvc.aestronglyMeasurable]
  have hexp (τ : ℝ) (hτ : τ ≤ -1) : v τ = Real.exp (1 * (τ - -1)) • v (-1) :=
    eq_exp_smul_of_hasDerivAt_smul_of_le
      (fun σ hσ ↦ by simpa [leftCap_of_le_neg_one hσ] using hv σ) hτ
  -- Split `(-∞, 0)` at `-1`: an exponential tail and a compact piece.
  have hsplit : Iio (0 : ℝ) ⊆ Iic (-1) ∪ Icc (-1) 0 := fun τ hτ ↦ by
    rcases le_total τ (-1) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, le_of_lt hτ⟩
  refine IntegrableOn.mono_set (IntegrableOn.union ?_ ?_) hsplit
  · have hi : IntegrableOn (fun τ ↦ Real.exp 2 * ‖v (-1)‖ ^ 2 * Real.exp (2 * τ)) (Iic (-1)) :=
      (integrableOn_exp_mul_Iic two_pos (-1)).const_mul _
    refine hi.congr_fun (fun τ hτ ↦ ?_) measurableSet_Iic
    have he : Real.exp (1 * (τ - -1)) ^ 2 = Real.exp 2 * Real.exp (2 * τ) := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    simp only [hexp τ hτ, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow, he]
    ring
  · exact ((hvc.norm.pow 2).continuousOn).integrableOn_compact isCompact_Icc

/-- No nonzero solution of the adjoint equation `w' = leftCap A w` is square integrable on the
whole line: before time `-1` it is `exp (-(τ + 1)) w(-1)`. -/
private theorem squareIntegrableSolutions_neg_leftCap (hA : Continuous A)
    (hsym : ∀ τ, (A τ).toLinearMap.IsSymmetric) :
    squareIntegrableSolutions (-leftCap A) = ⊥ := by
  refine eq_bot_iff.2 ((squareIntegrableSolutions_le_squareIntegrableSolutionsOn _ (Iio 0)).trans
    ((squareIntegrableSolutionsOn_neg_le_orthogonal (isSymmetric_leftCap hsym)
      Real.volume_Iio).trans ?_))
  rw [squareIntegrableSolutionsOn_leftCap_Iio hA, Submodule.top_orthogonal_eq_bot]

/-- The two index formulas for the trajectory operator of a continuous family of symmetric
operators with invertible limits `A±`, equated: the square-integrable solutions of `v' + A v = 0`
and `E` have the same total dimension as the square-integrable solutions of `w' = A w`, the
negative spectral subspace of `A⁻` and the positive spectral subspace of `A⁺`. -/
private theorem finrank_squareIntegrableSolutions_add_finrank (hA : Continuous A)
    (hsym : ∀ τ, (A τ).toLinearMap.IsSymmetric) {Aminus Aplus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus)) :
    Module.finrank ℝ (squareIntegrableSolutions A) + Module.finrank ℝ E =
      Module.finrank ℝ (squareIntegrableSolutions (-A)) +
        Module.finrank ℝ (Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Iio 0)) +
        Module.finrank ℝ (Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Ioi 0)) := by
  -- A continuous family with limits at both ends is bounded, so it has an `L∞` class.
  obtain ⟨M, hM⟩ := exists_forall_norm_le_of_tendsto hA hbot htop
  set AL := (memLp_top_of_bound (μ := volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
    hA.aestronglyMeasurable M (.of_forall hM)).toLp A
  have hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A := MemLp.coeFn_toLp _
  have hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric :=
    ContinuousLinearMap.isClosed_setOf_isSymmetric.mem_of_tendsto htop (.of_forall hsym)
  have h1 := WeakDerivStep.index_trajectoryOperator_eq_finrank_pointSpectralSubspace_sub_finrank
    hA (ContinuousLinearMap.isClosed_setOf_isSymmetric.mem_of_tendsto hbot (.of_forall hsym))
    hsymplus hα hminus hplus hbot htop AL hAL
  have h2 := WeakDerivStep.index_trajectoryOperator_eq_finrank_sub_finrank hA hsym hα hminus hplus
    hbot htop AL hAL
  -- The spectral subspaces of the invertible symmetric `A⁺` are complementary.
  have hker : LinearMap.ker (Aplus : E →ₗ[ℝ] E) = ⊥ := LinearMap.ker_eq_bot.2
    (ContinuousLinearMap.injective_of_forall_norm_le fun v ↦ (le_inv_mul_iff₀ hα).2 (hplus v))
  have hcompl := Submodule.finrank_add_eq_of_isCompl
    (hsymplus.isCompl_pointSpectralSubspace_Iio_zero_Ioi_zero hker)
  omega

/-- **The dimension of the stable solutions.** Let `A` be a continuous family of symmetric
operators on a finite-dimensional real inner product space, with an invertible limit `A⁺` at
`+∞`. Then the initial values of the solutions of `v' + A v = 0` square integrable on `(0, ∞)`
form a space of the dimension of the positive spectral subspace of `A⁺`: the number of positive
eigenvalues of `A⁺`, counted with multiplicity. -/
theorem finrank_squareIntegrableSolutionsOn_Ioi (hA : Continuous A)
    (hsym : ∀ τ, (A τ).toLinearMap.IsSymmetric) {Aplus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖) (htop : Tendsto A atTop (𝓝 Aplus)) :
    Module.finrank ℝ (squareIntegrableSolutionsOn A (Ioi 0)) =
      Module.finrank ℝ (Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Ioi 0)) := by
  -- Compute the index of the trajectory operator of the capped family in two ways.
  have hC := continuous_leftCap hA
  have hβ : 0 < min α 1 := lt_min hα one_pos
  have hminus' : ∀ v : E, min α 1 * ‖v‖ ≤ ‖(-ContinuousLinearMap.id ℝ E) v‖ := fun v ↦ by
    simpa using mul_le_of_le_one_left (norm_nonneg v) (min_le_right α 1)
  have hplus' : ∀ v : E, min α 1 * ‖v‖ ≤ ‖Aplus v‖ := fun v ↦
    (mul_le_mul_of_nonneg_right (min_le_left α 1) (norm_nonneg v)).trans (hplus v)
  have h := finrank_squareIntegrableSolutions_add_finrank hC (isSymmetric_leftCap hsym) hβ hminus'
    hplus' tendsto_leftCap_atBot (tendsto_leftCap_atTop htop)
  -- All eigenvalues of `-id` are negative.
  have hid : Module.End.pointSpectralSubspace
      ((-ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E) (Iio 0) = ⊤ :=
    eq_top_iff.2 fun x _ ↦ Module.End.eigenspace_le_pointSpectralSubspace
      (show (-1 : ℝ) ∈ Iio 0 by norm_num) (Module.End.mem_eigenspace_iff.2 (by simp))
  -- The kernel is the stable solutions of `A`, and there is no cokernel.
  rw [← squareIntegrableSolutionsOn_Iio_inf_Ioi hC, squareIntegrableSolutionsOn_leftCap_Iio hA,
    top_inf_eq, squareIntegrableSolutionsOn_Ioi_congr hC hA fun τ hτ ↦ leftCap_of_nonneg hτ,
    squareIntegrableSolutions_neg_leftCap hA hsym, finrank_bot, hid, finrank_top] at h
  omega

/-- **The dimension of the unstable solutions.** Let `A` be a continuous family of symmetric
operators on a finite-dimensional real inner product space, with an invertible limit `A⁻` at
`-∞`. Then the initial values of the solutions of `v' + A v = 0` square integrable on `(-∞, 0)`
form a space of the dimension of the negative spectral subspace of `A⁻`: the number of negative
eigenvalues of `A⁻`, counted with multiplicity. -/
theorem finrank_squareIntegrableSolutionsOn_Iio (hA : Continuous A)
    (hsym : ∀ τ, (A τ).toLinearMap.IsSymmetric) {Aminus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hbot : Tendsto A atBot (𝓝 Aminus)) :
    Module.finrank ℝ (squareIntegrableSolutionsOn A (Iio 0)) =
      Module.finrank ℝ (Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Iio 0)) := by
  rw [squareIntegrableSolutionsOn_Iio_eq_Ioi,
    finrank_squareIntegrableSolutionsOn_Ioi (A := fun τ ↦ -A (-τ)) (hA.comp continuous_neg).neg
      (fun τ ↦ (hsym (-τ)).neg) hα (Aplus := -Aminus) (by simpa using hminus)
      (hbot.comp tendsto_neg_atTop_atBot).neg,
    ContinuousLinearMap.toLinearMap_neg, Module.End.pointSpectralSubspace_neg, neg_Ioi, neg_zero]

/-! ### The cokernel of the trajectory operator -/

/-- **The cokernel of the trajectory operator is the failure of transversality.** Let `A` be a
continuous family of symmetric operators on a finite-dimensional real inner product space, with
invertible limits at `±∞`. Then the initial values of the square-integrable solutions of the
adjoint equation `w' = A w` are the orthogonal complement of the sum of the unstable and stable
solutions of `v' + A v = 0`, those square integrable on `(-∞, 0)` and on `(0, ∞)`. -/
theorem squareIntegrableSolutions_neg_eq_orthogonal_sup (hA : Continuous A)
    (hsym : ∀ τ, (A τ).toLinearMap.IsSymmetric) {Aminus Aplus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus)) :
    squareIntegrableSolutions (-A) =
      (squareIntegrableSolutionsOn A (Iio 0) ⊔ squareIntegrableSolutionsOn A (Ioi 0))ᗮ := by
  have hU := finrank_squareIntegrableSolutionsOn_Iio hA hsym hα hminus hbot
  have hW := finrank_squareIntegrableSolutionsOn_Ioi hA hsym hα hplus htop
  have hinf := squareIntegrableSolutionsOn_Iio_inf_Ioi hA
  set U := squareIntegrableSolutionsOn A (Iio 0)
  set W := squareIntegrableSolutionsOn A (Ioi 0)
  -- The adjoint solutions are orthogonal to the unstable and to the stable solutions.
  have hle : squareIntegrableSolutions (-A) ≤ (U ⊔ W)ᗮ := by
    rw [← Submodule.inf_orthogonal]
    exact le_inf
      ((squareIntegrableSolutions_le_squareIntegrableSolutionsOn _ _).trans
        (squareIntegrableSolutionsOn_neg_le_orthogonal hsym Real.volume_Iio))
      ((squareIntegrableSolutions_le_squareIntegrableSolutionsOn _ _).trans
        (squareIntegrableSolutionsOn_neg_le_orthogonal hsym Real.volume_Ioi))
  -- Equality by counting dimensions with the index formula.
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have h := finrank_squareIntegrableSolutions_add_finrank hA hsym hα hminus hplus hbot htop
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq U W
  have horth := (U ⊔ W).finrank_add_finrank_orthogonal
  rw [hinf] at hsup
  omega

/-- **The trajectory operator is onto exactly when the stable and unstable solutions span.** Let
`A` be a continuous family of symmetric operators on a finite-dimensional real inner product
space, with invertible limits at `±∞`. Then `D_A u = u' + A u` from `W^{1,2}(ℝ, E)` to
`L²(ℝ, E)` is surjective if and only if every vector of `E` is the sum of the value at time `0`
of a solution of `v' + A v = 0` square integrable on `(-∞, 0)` and of one square integrable on
`(0, ∞)`. -/
theorem WeakDerivStep.surjective_trajectoryOperator_iff_sup_eq_top (hA : Continuous A)
    (hsym : ∀ τ, (A τ).toLinearMap.IsSymmetric) {Aminus Aplus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    Function.Surjective (WeakDerivStep.trajectoryOperator (p := 2) AL) ↔
      squareIntegrableSolutionsOn A (Iio 0) ⊔ squareIntegrableSolutionsOn A (Ioi 0) = ⊤ := by
  have hclosed := WeakDerivStep.isClosed_range_trajectoryOperator_of_hasLyapunovForm hA
    (ContinuousLinearMap.hasLyapunovForm_of_tendsto_of_isSymmetric hsym hbot hα hminus)
    (ContinuousLinearMap.hasLyapunovForm_of_tendsto_of_isSymmetric hsym htop hα hplus) hbot htop
    AL hAL
  -- The coefficient is its own pointwise adjoint.
  have hadj : ∀ᵐ τ ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      AL τ = ContinuousLinearMap.adjoint (AL τ) := by
    filter_upwards [hAL] with τ hτ
    rw [hτ]
    exact (hsym τ).clm_adjoint_eq.symm
  have hnegAL : -AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] -A := by
    filter_upwards [Lp.coeFn_neg AL, hAL] with τ hτ hAτ
    simp only [hτ, Pi.neg_apply, hAτ]
  rw [WeakDerivStep.surjective_trajectoryOperator_iff_ker_neg_eq_bot hadj hclosed,
    WeakDerivStep.ker_trajectoryOperator_eq_bot_iff hA.neg (-AL) hnegAL,
    squareIntegrableSolutions_neg_eq_orthogonal_sup hA hsym hα hminus hplus hbot htop,
    Submodule.orthogonal_eq_bot_iff]

end Dimension

end TauCeti
