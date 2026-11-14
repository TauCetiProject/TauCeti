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

For a continuous family whose limits `A±` at `±∞` have Lyapunov forms (no symmetry of `A` is
assumed) this file computes their dimensions and identifies the cokernel of `D_A` with the failure
of the stable and unstable solutions to span `E`:

* if `S` is a symmetric Lyapunov form of `A⁺`, the stable solutions have dimension `dim E - n⁻(S)`
  and the stable solutions of the formal adjoint equation `w' = A† w` have dimension `n⁻(S)`, where
  `n⁻` counts negative eigenvalues
  (`TauCeti.finrank_squareIntegrableSolutionsOn_Ioi_add_finrank_pointSpectralSubspace`,
  `TauCeti.finrank_squareIntegrableSolutionsOn_neg_adjoint_Ioi`); for a symmetric invertible `A⁺`
  this is the dimension of its positive spectral subspace
  (`TauCeti.finrank_squareIntegrableSolutionsOn_Ioi`), and dually at `-∞`
  (`TauCeti.finrank_squareIntegrableSolutionsOn_Iio`);
* on each half-line the decaying solutions of the adjoint equation are the orthogonal complement of
  those of `v' + A v = 0` (`TauCeti.squareIntegrableSolutionsOn_neg_adjoint_Ioi_eq_orthogonal`,
  `TauCeti.squareIntegrableSolutionsOn_neg_adjoint_Iio_eq_orthogonal`);
* so the square-integrable solutions of the adjoint equation, which model the cokernel of `D_A`,
  are the orthogonal complement of the sum of the stable and unstable solutions
  (`TauCeti.squareIntegrableSolutions_neg_adjoint_eq_orthogonal_sup`);
* hence `D_A` is surjective exactly when the stable and unstable solutions span `E`
  (`TauCeti.WeakDerivStep.surjective_trajectoryOperator_iff_sup_eq_top`).

For the linearized gradient flow the last statement is the linear half of the classical fact that
the linearized operator is onto exactly when the unstable and stable sets meet transversally along
`γ`, which compares the Fredholm description of the spaces of gradient trajectories with their
description as intersections of unstable and stable sets.

## Proofs

If `v` solves `v' = -A v` and `w` solves the adjoint equation `w' = A† w`, then `⟪v, w⟫` is
constant. When both are square integrable on a half-line this constant is integrable there, hence
zero; so the adjoint solutions square integrable on a half-line are orthogonal to the solutions
square integrable on the same half-line (`TauCeti.squareIntegrableSolutionsOn_neg_le_orthogonal`).
Equality is a dimension count at each end.

The dimensions are computed with two index formulas for the trajectory operator, one through the
square-integrable solutions of the equation and of its adjoint, and one through the inertia of
the Lyapunov forms of the limits (both in the namespace `TauCeti.WeakDerivStep`:
`index_trajectoryOperator_eq_finrank_sub_finrank_of_hasLyapunovForm` and
`index_trajectoryOperator_eq_finrank_pointSpectralSubspace_sub_finrank_of_forall_le_inner`). The
stable solutions only depend on `A` on `[0, ∞)` (`TauCeti.squareIntegrableSolutionsOn_Ioi_congr`),
so `A` may be replaced on `(-∞, 0]` by a family equal to `∓1` before time `-1`. There every
solution of one of the two equations decays on `(-∞, 0)` and no nonzero solution of the other does,
so one of the two whole-line spaces is the stable space of `A` or of its adjoint and the other is
zero. The statements at `-∞` follow by reflecting time: the unstable solutions of `A` are the
stable solutions of the reflected family `s ↦ -A(-s)`
(`TauCeti.squareIntegrableSolutionsOn_Iio_eq_Ioi`).

## References

* K. J. Palmer, *Exponential dichotomies and transversal homoclinic points*, J. Differential
  Equations **55** (1984), 225--256, Lemma 4.2 (the range of `d/ds + A` and the adjoint
  equation).
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {A B : ℝ → E →L[ℝ] E}
  {s : Set ℝ}

/-- **Adjoint solutions decaying on a set are orthogonal to solutions decaying there.** Let `B` be
pointwise adjoint to `A`: `⟪A τ x, y⟫ = ⟪x, B τ y⟫`. If `v' = -A v` and `w' = B w`, then
`⟪v, w⟫` is constant. When `v` and `w` are square integrable on a set `s` of infinite measure,
such as a half-line, this constant is integrable on `s`, hence zero. So the solutions of the
adjoint equation `w' = B w` square integrable on `s` are orthogonal to the solutions of
`v' + A v = 0` square integrable on `s`. -/
theorem squareIntegrableSolutionsOn_neg_le_orthogonal
    (hAB : ∀ τ x y, ⟪A τ x, y⟫_ℝ = ⟪x, B τ y⟫_ℝ) (hs : volume s = ∞) :
    squareIntegrableSolutionsOn (fun τ ↦ -B τ) s ≤ (squareIntegrableSolutionsOn A s)ᗮ := by
  rintro _ ⟨w, rfl, hw, hw2⟩
  refine (Submodule.mem_orthogonal _ _).2 fun _ ⟨v, hv0, hv, hv2⟩ ↦ ?_
  subst hv0
  -- The pairing `⟪v, w⟫` has derivative `⟪-A v, w⟫ + ⟪v, B w⟫ = 0`, so it is constant.
  have hderiv (τ : ℝ) : HasDerivAt (fun τ ↦ ⟪v τ, w τ⟫_ℝ) 0 τ := by
    have h := (hv τ).inner ℝ (hw τ)
    rwa [neg_apply, neg_neg, inner_neg_left, hAB, add_neg_cancel] at h
  have hconst (τ : ℝ) : ⟪v τ, w τ⟫_ℝ = ⟪v 0, w 0⟫_ℝ :=
    is_const_of_deriv_eq_zero (fun τ ↦ (hderiv τ).differentiableAt) (fun τ ↦ (hderiv τ).deriv)
      τ 0
  -- A product of two square-integrable functions is integrable, by Hölder's inequality.
  have hint : IntegrableOn (fun τ ↦ ⟪v τ, w τ⟫_ℝ) s :=
    memLp_one_iff_integrable.1 ((innerSL ℝ).memLp_of_bilin 1 hv2 hw2)
  simp_rw [hconst] at hint
  rw [integrableOn_const_iff, hs] at hint
  simpa using hint

/-- If every solution of `v' + A v = 0` is square integrable on `(-∞, 0)`, then no nonzero
solution of the adjoint equation `w' = B w` is. -/
private theorem squareIntegrableSolutionsOn_Iio_eq_bot
    (hAB : ∀ τ x y, ⟪A τ x, y⟫_ℝ = ⟪x, B τ y⟫_ℝ)
    (hA : squareIntegrableSolutionsOn A (Iio 0) = ⊤) :
    squareIntegrableSolutionsOn (fun τ ↦ -B τ) (Iio 0) = ⊥ :=
  eq_bot_iff.2 ((squareIntegrableSolutionsOn_neg_le_orthogonal hAB Real.volume_Iio).trans
    (by rw [hA, Submodule.top_orthogonal_eq_bot]))

end InnerProduct

/-! ### The dimensions of the stable and unstable solutions -/

section Dimension

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {A : ℝ → E →L[ℝ] E}

/-- The family `A` capped on the left by `C`: equal to `A` on `[0, ∞)` and to `C` on `(-∞, -1]`,
interpolating by Mathlib's smooth transition function in between. -/
private def leftCap (A : ℝ → E →L[ℝ] E) (C : E →L[ℝ] E) (τ : ℝ) : E →L[ℝ] E :=
  Real.smoothTransition (-τ) • C + (1 - Real.smoothTransition (-τ)) • A τ

private theorem leftCap_of_nonneg {C : E →L[ℝ] E} {τ : ℝ} (hτ : 0 ≤ τ) :
    leftCap A C τ = A τ := by
  simp [leftCap, Real.smoothTransition.zero_of_nonpos (neg_nonpos.2 hτ)]

private theorem leftCap_of_le_neg_one {C : E →L[ℝ] E} {τ : ℝ} (hτ : τ ≤ -1) :
    leftCap A C τ = C := by
  simp [leftCap, Real.smoothTransition.one_of_one_le (le_neg_of_le_neg hτ)]

private theorem continuous_leftCap (hA : Continuous A) (C : E →L[ℝ] E) :
    Continuous (leftCap A C) :=
  ((Real.smoothTransition.continuous.comp continuous_neg).smul continuous_const).add
    ((continuous_const.sub (Real.smoothTransition.continuous.comp continuous_neg)).smul hA)

private theorem tendsto_leftCap_atBot (C : E →L[ℝ] E) : Tendsto (leftCap A C) atBot (𝓝 C) :=
  tendsto_const_nhds.congr' <| (eventually_le_atBot (-1)).mono fun _ hτ ↦
    (leftCap_of_le_neg_one hτ).symm

private theorem tendsto_leftCap_atTop {Aplus : E →L[ℝ] E} (htop : Tendsto A atTop (𝓝 Aplus))
    (C : E →L[ℝ] E) : Tendsto (leftCap A C) atTop (𝓝 Aplus) :=
  htop.congr' <| (eventually_ge_atTop 0).mono fun _ hτ ↦ (leftCap_of_nonneg hτ).symm

variable [FiniteDimensional ℝ E]

/-- Every solution of `v' + B v = 0` is square integrable on `(-∞, 0)` when `B = -1` before
time `-1`: there it is `exp (τ + 1) v(-1)`. -/
private theorem squareIntegrableSolutionsOn_Iio_eq_top {B : ℝ → E →L[ℝ] E} (hB : Continuous B)
    (hB₁ : ∀ τ ≤ -1, B τ = -1) : squareIntegrableSolutionsOn B (Iio 0) = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  set v : ℝ → E := fun τ ↦ dysonSeriesLeft (-B) τ x
  have hv (τ : ℝ) : HasDerivAt v (-B τ (v τ)) τ := by
    simpa [v] using hasDerivAt_dysonSeriesLeft_apply hB.neg x τ
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun τ ↦ (hv τ).continuousAt
  refine ⟨v, by simp [v], hv, ?_⟩
  rw [memLp_two_iff_integrable_sq_norm hvc.aestronglyMeasurable]
  have hexp (τ : ℝ) (hτ : τ ≤ -1) : v τ = Real.exp (1 * (τ - -1)) • v (-1) :=
    eq_exp_smul_of_hasDerivAt_smul_of_le (fun σ hσ ↦ by simpa [hB₁ σ hσ] using hv σ) hτ
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

open WeakDerivStep in
/-- The index of the trajectory operator of `leftCap A C`, for an operator `C` that is its own
symmetric Lyapunov form (such as `C = ±1`), computed in two ways: by the square-integrable
solutions of the equation and of its formal adjoint, and by the negative inertia of the Lyapunov
forms `C` and `S` of its two limits. -/
private theorem finrank_sub_finrank_leftCap (hA : Continuous A) {C Aplus S : E →L[ℝ] E}
    (hC : (C : E →ₗ[ℝ] E).IsSymmetric) (hCC : ∀ v, 1 * ‖v‖ ^ 2 ≤ ⟪C (C v), v⟫_ℝ)
    (hS : (S : E →ₗ[ℝ] E).IsSymmetric) {c : ℝ} (hc : 0 < c)
    (hplus : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪S (Aplus v), v⟫_ℝ) (htop : Tendsto A atTop (𝓝 Aplus)) :
    (Module.finrank ℝ (squareIntegrableSolutions (leftCap A C)) : ℤ) -
        Module.finrank ℝ
          (squareIntegrableSolutions fun τ ↦ -ContinuousLinearMap.adjoint (leftCap A C τ)) =
      Module.finrank ℝ (Module.End.pointSpectralSubspace (C : E →ₗ[ℝ] E) (Iio 0)) -
        Module.finrank ℝ (Module.End.pointSpectralSubspace (S : E →ₗ[ℝ] E) (Iio 0)) := by
  have hB := continuous_leftCap hA C
  have hBbot := tendsto_leftCap_atBot (A := A) C
  have hBtop := tendsto_leftCap_atTop htop C
  -- A continuous family with limits at both ends is bounded, so it has an `L∞` class.
  obtain ⟨M, hM⟩ := exists_forall_norm_le_of_tendsto hB hBbot hBtop
  set BL := (memLp_top_of_bound (μ := volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
    hB.aestronglyMeasurable M (.of_forall hM)).toLp (leftCap A C)
  have hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] leftCap A C := MemLp.coeFn_toLp _
  rw [← index_trajectoryOperator_eq_finrank_sub_finrank_of_hasLyapunovForm hB
      (ContinuousLinearMap.hasLyapunovForm_iff.2 ⟨C, hC, 1, one_pos, hCC⟩)
      (ContinuousLinearMap.hasLyapunovForm_iff.2 ⟨S, hS, c, hc, hplus⟩) hBbot hBtop BL hBL,
    index_trajectoryOperator_eq_finrank_pointSpectralSubspace_sub_finrank_of_forall_le_inner hB hC
      hS one_pos hc hCC hplus hBbot hBtop BL hBL]

/-- **The dimension of the stable solutions.** Let `A` be a continuous family of operators on a
finite-dimensional real inner product space tending at `+∞` to an operator `A⁺` with a symmetric
Lyapunov form `S`: `c ‖v‖² ≤ ⟪S (A⁺ v), v⟫` with `c > 0`. Then the initial values of the
solutions of `v' + A v = 0` square integrable on `(0, ∞)` form a space of dimension
`dim E - n⁻(S)`, where `n⁻(S)` is the number of negative eigenvalues of `S`. -/
theorem finrank_squareIntegrableSolutionsOn_Ioi_add_finrank_pointSpectralSubspace
    (hA : Continuous A) {Aplus S : E →L[ℝ] E} (hS : (S : E →ₗ[ℝ] E).IsSymmetric) {c : ℝ}
    (hc : 0 < c) (hplus : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪S (Aplus v), v⟫_ℝ)
    (htop : Tendsto A atTop (𝓝 Aplus)) :
    Module.finrank ℝ (squareIntegrableSolutionsOn A (Ioi 0)) +
        Module.finrank ℝ (Module.End.pointSpectralSubspace (S : E →ₗ[ℝ] E) (Iio 0)) =
      Module.finrank ℝ E := by
  have hsym : ((-1 : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric := by
    rw [ContinuousLinearMap.toLinearMap_neg, ContinuousLinearMap.toLinearMap_one]
    exact LinearMap.IsSymmetric.one.neg
  have h := finrank_sub_finrank_leftCap hA hsym (by simp) hS hc hplus htop
  set B := leftCap A (-1)
  have hB : Continuous B := continuous_leftCap hA _
  have hBadj : Continuous fun τ ↦ -ContinuousLinearMap.adjoint (B τ) :=
    (ContinuousLinearMap.adjoint.continuous.comp hB).neg
  -- At `-∞`, where `B = -1`, every solution of `v' + B v = 0` decays and no nonzero solution of
  -- the adjoint equation does.
  have hU : squareIntegrableSolutionsOn B (Iio 0) = ⊤ :=
    squareIntegrableSolutionsOn_Iio_eq_top hB fun τ hτ ↦ leftCap_of_le_neg_one hτ
  have hU' := squareIntegrableSolutionsOn_Iio_eq_bot
    (fun τ x y ↦ (ContinuousLinearMap.adjoint_inner_right (B τ) x y).symm) hU
  -- All eigenvalues of `-1` are negative.
  have hneg : Module.End.pointSpectralSubspace ((-1 : E →L[ℝ] E) : E →ₗ[ℝ] E) (Iio 0) = ⊤ := by
    simpa using Module.End.pointSpectralSubspace_smul_one_of_mem (𝕜 := ℝ) (E := E) (μ := -1)
      (Ω := Iio 0) (by norm_num)
  -- So the whole-line solutions of `B` are the stable solutions of `A`, and those of the adjoint
  -- equation vanish.
  have hsol : squareIntegrableSolutions B = squareIntegrableSolutionsOn A (Ioi 0) := by
    rw [← squareIntegrableSolutionsOn_Iio_inf_Ioi hB, hU, top_inf_eq]
    exact squareIntegrableSolutionsOn_Ioi_congr hB hA fun τ hτ ↦ leftCap_of_nonneg hτ
  have hsol' : squareIntegrableSolutions (fun τ ↦ -ContinuousLinearMap.adjoint (B τ)) = ⊥ := by
    rw [← squareIntegrableSolutionsOn_Iio_inf_Ioi hBadj, hU', bot_inf_eq]
  simp only [hsol, hsol', hneg, finrank_bot, finrank_top] at h
  omega

/-- **The dimension of the stable solutions of the adjoint equation.** Let `A` be a continuous
family of operators on a finite-dimensional real inner product space tending at `+∞` to an
operator `A⁺` with a symmetric Lyapunov form `S`: `c ‖v‖² ≤ ⟪S (A⁺ v), v⟫` with `c > 0`. Then
the initial values of the solutions of the formal adjoint equation `w' = A† w` square integrable
on `(0, ∞)` form a space of dimension `n⁻(S)`, the number of negative eigenvalues of `S`. -/
theorem finrank_squareIntegrableSolutionsOn_neg_adjoint_Ioi
    (hA : Continuous A) {Aplus S : E →L[ℝ] E} (hS : (S : E →ₗ[ℝ] E).IsSymmetric) {c : ℝ}
    (hc : 0 < c) (hplus : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪S (Aplus v), v⟫_ℝ)
    (htop : Tendsto A atTop (𝓝 Aplus)) :
    Module.finrank ℝ
        (squareIntegrableSolutionsOn (fun τ ↦ -ContinuousLinearMap.adjoint (A τ)) (Ioi 0)) =
      Module.finrank ℝ (Module.End.pointSpectralSubspace (S : E →ₗ[ℝ] E) (Iio 0)) := by
  have hsym : ((1 : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric := by
    rw [ContinuousLinearMap.toLinearMap_one]
    exact LinearMap.IsSymmetric.one
  have h := finrank_sub_finrank_leftCap hA hsym (by simp) hS hc hplus htop
  set B := leftCap A 1
  have hB : Continuous B := continuous_leftCap hA _
  have hBadj : Continuous fun τ ↦ -ContinuousLinearMap.adjoint (B τ) :=
    (ContinuousLinearMap.adjoint.continuous.comp hB).neg
  have hAadj : Continuous fun τ ↦ -ContinuousLinearMap.adjoint (A τ) :=
    (ContinuousLinearMap.adjoint.continuous.comp hA).neg
  -- At `-∞`, where `B = 1`, every solution of the adjoint equation decays and no nonzero solution
  -- of `v' + B v = 0` does.
  have hU' : squareIntegrableSolutionsOn (fun τ ↦ -ContinuousLinearMap.adjoint (B τ)) (Iio 0) =
      ⊤ :=
    squareIntegrableSolutionsOn_Iio_eq_top hBadj fun τ hτ ↦ by
      simp [B, leftCap_of_le_neg_one hτ, ContinuousLinearMap.adjoint_one]
  have hU : squareIntegrableSolutionsOn B (Iio 0) = ⊥ := by
    simpa using squareIntegrableSolutionsOn_Iio_eq_bot (B := fun τ ↦ -B τ)
      (fun τ x y ↦ by
        simp [inner_neg_left, inner_neg_right, ContinuousLinearMap.adjoint_inner_left]) hU'
  -- No eigenvalue of `1` is negative.
  have hpos : Module.End.pointSpectralSubspace ((1 : E →L[ℝ] E) : E →ₗ[ℝ] E) (Iio 0) = ⊥ := by
    simpa using Module.End.pointSpectralSubspace_smul_one_of_notMem (𝕜 := ℝ) (E := E) (μ := 1)
      (Ω := Iio 0) (by norm_num)
  -- So the whole-line solutions of `B` vanish, and those of the adjoint equation are the stable
  -- solutions of the adjoint equation of `A`.
  have hsol : squareIntegrableSolutions B = ⊥ := by
    rw [← squareIntegrableSolutionsOn_Iio_inf_Ioi hB, hU, bot_inf_eq]
  have hsol' : squareIntegrableSolutions (fun τ ↦ -ContinuousLinearMap.adjoint (B τ)) =
      squareIntegrableSolutionsOn (fun τ ↦ -ContinuousLinearMap.adjoint (A τ)) (Ioi 0) := by
    rw [← squareIntegrableSolutionsOn_Iio_inf_Ioi hBadj, hU', top_inf_eq]
    exact squareIntegrableSolutionsOn_Ioi_congr hBadj hAadj fun τ hτ ↦ by
      simp [B, leftCap_of_nonneg hτ]
  simp only [hsol, hsol', hpos, finrank_bot] at h
  omega

/-- **The dimension of the stable solutions for an invertible symmetric limit.** Let `A` be a
continuous family of operators on a finite-dimensional real inner product space tending at `+∞`
to a symmetric operator `A⁺` with `α ‖v‖ ≤ ‖A⁺ v‖`, `α > 0`. Then the initial values of the
solutions of `v' + A v = 0` square integrable on `(0, ∞)` form a space of the dimension of the
positive spectral subspace of `A⁺`: the number of positive eigenvalues of `A⁺`, counted with
multiplicity. -/
theorem finrank_squareIntegrableSolutionsOn_Ioi (hA : Continuous A) {Aplus : E →L[ℝ] E}
    (hsym : (Aplus : E →ₗ[ℝ] E).IsSymmetric) {α : ℝ} (hα : 0 < α)
    (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖) (htop : Tendsto A atTop (𝓝 Aplus)) :
    Module.finrank ℝ (squareIntegrableSolutionsOn A (Ioi 0)) =
      Module.finrank ℝ (Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Ioi 0)) := by
  -- `A⁺` is its own Lyapunov form.
  have hform : ∀ v, α ^ 2 * ‖v‖ ^ 2 ≤ ⟪Aplus (Aplus v), v⟫_ℝ := fun v ↦ by
    rw [hsym.apply_clm, real_inner_self_eq_norm_sq, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (hplus v) 2
  have h₁ := finrank_squareIntegrableSolutionsOn_Ioi_add_finrank_pointSpectralSubspace hA hsym
    (by positivity) hform htop
  -- The spectral subspaces of the invertible symmetric `A⁺` are complementary.
  have hker : LinearMap.ker (Aplus : E →ₗ[ℝ] E) = ⊥ := LinearMap.ker_eq_bot.2
    (ContinuousLinearMap.injective_of_forall_norm_le fun v ↦ (le_inv_mul_iff₀ hα).2 (hplus v))
  have h₂ :=
    (Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Ioi 0)).finrank_add_finrank_orthogonal
  rw [hsym.orthogonal_pointSpectralSubspace_Ioi_zero hker] at h₂
  omega

/-- **The dimension of the unstable solutions for an invertible symmetric limit.** Let `A` be a
continuous family of operators on a finite-dimensional real inner product space tending at `-∞`
to a symmetric operator `A⁻` with `α ‖v‖ ≤ ‖A⁻ v‖`, `α > 0`. Then the initial values of the
solutions of `v' + A v = 0` square integrable on `(-∞, 0)` form a space of the dimension of the
negative spectral subspace of `A⁻`: the number of negative eigenvalues of `A⁻`, counted with
multiplicity. -/
theorem finrank_squareIntegrableSolutionsOn_Iio (hA : Continuous A) {Aminus : E →L[ℝ] E}
    (hsym : (Aminus : E →ₗ[ℝ] E).IsSymmetric) {α : ℝ} (hα : 0 < α)
    (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hbot : Tendsto A atBot (𝓝 Aminus)) :
    Module.finrank ℝ (squareIntegrableSolutionsOn A (Iio 0)) =
      Module.finrank ℝ (Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Iio 0)) := by
  rw [squareIntegrableSolutionsOn_Iio_eq_Ioi,
    finrank_squareIntegrableSolutionsOn_Ioi (A := fun τ ↦ -A (-τ)) (hA.comp continuous_neg).neg
      (by rw [ContinuousLinearMap.toLinearMap_neg]; exact hsym.neg) hα (Aplus := -Aminus)
      (by simpa using hminus) (hbot.comp tendsto_neg_atTop_atBot).neg,
    ContinuousLinearMap.toLinearMap_neg, Module.End.pointSpectralSubspace_neg, neg_Ioi, neg_zero]

/-! ### The cokernel of the trajectory operator -/

/-- **The stable solutions of the adjoint equation are the orthogonal complement.** Let `A` be a
continuous family of operators on a finite-dimensional real inner product space tending at `+∞`
to an operator with a Lyapunov form. Then the initial values of the solutions of the formal
adjoint equation `w' = A† w` square integrable on `(0, ∞)` are exactly the vectors orthogonal to
the initial values of the solutions of `v' + A v = 0` square integrable on `(0, ∞)`. -/
theorem squareIntegrableSolutionsOn_neg_adjoint_Ioi_eq_orthogonal (hA : Continuous A)
    {Aplus : E →L[ℝ] E} (hplus : Aplus.HasLyapunovForm) (htop : Tendsto A atTop (𝓝 Aplus)) :
    squareIntegrableSolutionsOn (fun τ ↦ -ContinuousLinearMap.adjoint (A τ)) (Ioi 0) =
      (squareIntegrableSolutionsOn A (Ioi 0))ᗮ := by
  obtain ⟨S, hS, c, hc, hcS⟩ := ContinuousLinearMap.hasLyapunovForm_iff.1 hplus
  refine Submodule.eq_of_le_of_finrank_eq
    (squareIntegrableSolutionsOn_neg_le_orthogonal
      (fun τ x y ↦ (ContinuousLinearMap.adjoint_inner_right (A τ) x y).symm) Real.volume_Ioi) ?_
  have h₁ := finrank_squareIntegrableSolutionsOn_Ioi_add_finrank_pointSpectralSubspace hA hS hc
    hcS htop
  have h₂ := finrank_squareIntegrableSolutionsOn_neg_adjoint_Ioi hA hS hc hcS htop
  have h₃ := (squareIntegrableSolutionsOn A (Ioi 0)).finrank_add_finrank_orthogonal
  omega

/-- **The unstable solutions of the adjoint equation are the orthogonal complement.** Let `A` be
a continuous family of operators on a finite-dimensional real inner product space tending at `-∞`
to an operator with a Lyapunov form. Then the initial values of the solutions of the formal
adjoint equation `w' = A† w` square integrable on `(-∞, 0)` are exactly the vectors orthogonal to
the initial values of the solutions of `v' + A v = 0` square integrable on `(-∞, 0)`. -/
theorem squareIntegrableSolutionsOn_neg_adjoint_Iio_eq_orthogonal (hA : Continuous A)
    {Aminus : E →L[ℝ] E} (hminus : Aminus.HasLyapunovForm) (hbot : Tendsto A atBot (𝓝 Aminus)) :
    squareIntegrableSolutionsOn (fun τ ↦ -ContinuousLinearMap.adjoint (A τ)) (Iio 0) =
      (squareIntegrableSolutionsOn A (Iio 0))ᗮ := by
  -- Reverse time: `A` becomes `τ ↦ -A (-τ)`, which tends to `-A⁻` at `+∞`.
  have h := squareIntegrableSolutionsOn_neg_adjoint_Ioi_eq_orthogonal
    (A := fun τ ↦ -A (-τ)) (hA.comp continuous_neg).neg hminus.neg
    (hbot.comp tendsto_neg_atTop_atBot).neg
  rw [squareIntegrableSolutionsOn_Iio_eq_Ioi, squareIntegrableSolutionsOn_Iio_eq_Ioi, ← h]
  simp

/-- **The cokernel of the trajectory operator is the failure of transversality.** Let `A` be a
continuous family of operators on a finite-dimensional real inner product space whose limits at
`±∞` have Lyapunov forms. Then the initial values of the square-integrable solutions of the formal
adjoint equation `w' = A† w`, which model the cokernel of `D_A`, are the orthogonal complement of
the sum of the unstable and stable solutions of `v' + A v = 0`, those square integrable on
`(-∞, 0)` and on `(0, ∞)`. -/
theorem squareIntegrableSolutions_neg_adjoint_eq_orthogonal_sup (hA : Continuous A)
    {Aminus Aplus : E →L[ℝ] E} (hminus : Aminus.HasLyapunovForm) (hplus : Aplus.HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus)) :
    squareIntegrableSolutions (fun τ ↦ -ContinuousLinearMap.adjoint (A τ)) =
      (squareIntegrableSolutionsOn A (Iio 0) ⊔ squareIntegrableSolutionsOn A (Ioi 0))ᗮ := by
  have hAadj : Continuous fun τ ↦ -ContinuousLinearMap.adjoint (A τ) :=
    (ContinuousLinearMap.adjoint.continuous.comp hA).neg
  rw [← squareIntegrableSolutionsOn_Iio_inf_Ioi hAadj,
    squareIntegrableSolutionsOn_neg_adjoint_Iio_eq_orthogonal hA hminus hbot,
    squareIntegrableSolutionsOn_neg_adjoint_Ioi_eq_orthogonal hA hplus htop,
    Submodule.inf_orthogonal]

/-- **The trajectory operator is onto exactly when the stable and unstable solutions span.** Let
`A` be a continuous family of operators on a finite-dimensional real inner product space whose
limits at `±∞` have Lyapunov forms. Then `D_A u = u' + A u` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is
surjective if and only if every vector of `E` is the sum of the value at time `0` of a solution
of `v' + A v = 0` square integrable on `(-∞, 0)` and of one square integrable on `(0, ∞)`. -/
theorem WeakDerivStep.surjective_trajectoryOperator_iff_sup_eq_top (hA : Continuous A)
    {Aminus Aplus : E →L[ℝ] E} (hminus : Aminus.HasLyapunovForm) (hplus : Aplus.HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    Function.Surjective (WeakDerivStep.trajectoryOperator (p := 2) AL) ↔
      squareIntegrableSolutionsOn A (Iio 0) ⊔ squareIntegrableSolutionsOn A (Ioi 0) = ⊤ := by
  obtain ⟨BL, hBL⟩ := WeakDerivStep.exists_ae_eq_adjoint AL hAL
  have hneg : -BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun τ ↦ -ContinuousLinearMap.adjoint (A τ) := by
    filter_upwards [Lp.coeFn_neg BL, hBL] with τ hτ hBτ
    simp only [hτ, Pi.neg_apply, hBτ]
  have hAadj : Continuous fun τ ↦ -ContinuousLinearMap.adjoint (A τ) :=
    (ContinuousLinearMap.adjoint.continuous.comp hA).neg
  rw [WeakDerivStep.surjective_trajectoryOperator_iff_ker_neg_eq_bot
      (WeakDerivStep.ae_eq_adjoint_of_ae_eq hAL hBL)
      (WeakDerivStep.isClosed_range_trajectoryOperator_of_hasLyapunovForm hA hminus hplus hbot
        htop AL hAL),
    WeakDerivStep.ker_trajectoryOperator_eq_bot_iff hAadj (-BL) hneg,
    squareIntegrableSolutions_neg_adjoint_eq_orthogonal_sup hA hminus hplus hbot htop,
    Submodule.orthogonal_eq_bot_iff]

end Dimension

end TauCeti
