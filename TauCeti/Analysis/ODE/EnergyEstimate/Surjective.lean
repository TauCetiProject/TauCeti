/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.EnergyEstimate.Index
public import TauCeti.Analysis.ODE.TrajectoryOperator.HalfLine
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn

/-!
# Surjectivity of the trajectory operator and the decaying solutions at the two ends

Let `A` be a continuous family of operators on a finite-dimensional real inner product space `E`
whose limits `A±` at `±∞` have Lyapunov forms, so that the trajectory operator

`D_A u = u' + A u : W^{1,2}(ℝ, E) → L²(ℝ, E)`

is Fredholm. Write `U` for the initial values of the solutions of `v' + A v = 0` that are square
integrable on `(-∞, 0)` (`TauCeti.squareIntegrableSolutionsAtBot A`) and `S` for those square
integrable on `(0, ∞)` (`TauCeti.squareIntegrableSolutionsAtTop A`). The kernel of `D_A` is
`U ⊓ S` (`TauCeti.squareIntegrableSolutions_eq_inf`). This file identifies the cokernel:
the corresponding spaces of the formal adjoint equation `w' = A† w` are the orthogonal
complements `Uᗮ` and `Sᗮ`, so the cokernel of `D_A` is `(U ⊔ S)ᗮ`, and

`D_A` is onto `↔ U ⊔ S = E`.

For the linearized operator along a gradient trajectory `γ` from `p` to `q`, `U` and `S` are the
linearizations of the unstable manifold of `p` and of the stable manifold of `q` at `γ 0`, so this
is the analytic form of the transversality condition of Morse--Smale theory.

Orthogonality of the decaying solutions of the equation and of its adjoint is
`TauCeti.squareIntegrableSolutionsAtTop_neg_le_orthogonal`, which needs no hypothesis on the
limits. Equality is a dimension count, `dim S + dim S' = dim E` for the adjoint space `S'`. To
count, the family is replaced by one that agrees with it on `(-1, ∞)` and is the constant `∓1`
on `(-∞, -2]`. At such an end every solution of one of the two equations decays and only zero
does for the other, so one of the two whole-line spaces is `S` or `S'` and the other is zero.
The index theorem for limits with Lyapunov forms (`TauCeti.Analysis.ODE.EnergyEstimate.Index`)
then computes `dim S = dim E - n⁻(P)` and `dim S' = n⁻(P)`, where `P` is a symmetric Lyapunov
form of `A⁺` and `n⁻` counts negative eigenvalues. The statements at `-∞` follow by reversing
time.

## Main results

* `TauCeti.finrank_squareIntegrableSolutionsAtTop_add_finrank_pointSpectralSubspace` and
  `TauCeti.finrank_squareIntegrableSolutionsAtTop_neg_adjoint`: the two dimension counts at `+∞`.
* `TauCeti.squareIntegrableSolutionsAtTop_neg_adjoint_eq_orthogonal` and
  `TauCeti.squareIntegrableSolutionsAtBot_neg_adjoint_eq_orthogonal`: the adjoint half-line spaces
  are the orthogonal complements.
* `TauCeti.squareIntegrableSolutions_neg_adjoint_eq_orthogonal_sup`: the square-integrable
  solutions of the adjoint equation, which model the cokernel of `D_A`, are `(U ⊔ S)ᗮ`.
* `TauCeti.WeakDerivStep.surjective_trajectoryOperator_iff_sup_eq_top`: `D_A` is onto exactly
  when `U ⊔ S = E`.
* `TauCeti.finrank_squareIntegrableSolutionsAtBot_of_isSymmetric` and
  `TauCeti.finrank_squareIntegrableSolutionsAtTop_of_isSymmetric`: for invertible symmetric
  limits, `dim U` is the number of negative eigenvalues of `A⁻` and `dim S` the number of positive
  eigenvalues of `A⁺`.

## References

* M. Schwarz, *Morse Homology*, Birkhäuser, 1993, Chapter 2.
* K. J. Palmer, *Exponential dichotomies and transversal homoclinic points*, J. Differential
  Equations **55** (1984), 225--256, Lemma 4.2 (the range of `d/ds + A` and the adjoint
  equation).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter Set
open scoped ENNReal Topology InnerProductSpace

namespace TauCeti

open WeakDerivStep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {A : ℝ → E →L[ℝ] E}


/-- The family equal to `A` on `[-1, ∞)` and to `C` on `(-∞, -2]`, interpolating linearly in
between. -/
private def splice (A : ℝ → E →L[ℝ] E) (C : E →L[ℝ] E) (s : ℝ) : E →L[ℝ] E :=
  A (max s (-1)) + max 0 (min 1 (-1 - s)) • (C - A (-1))

private theorem continuous_splice (hA : Continuous A) (C : E →L[ℝ] E) :
    Continuous (splice A C) :=
  (hA.comp (continuous_id.max continuous_const)).add
    ((continuous_const.max (continuous_const.min (continuous_const.sub continuous_id))).smul
      continuous_const)

private theorem splice_of_lt (C : E →L[ℝ] E) {s : ℝ} (hs : -1 < s) : splice A C s = A s := by
  simp [splice, max_eq_left hs.le, min_eq_right (by linarith : -1 - s ≤ 1),
    max_eq_left (by linarith : -1 - s ≤ 0)]

private theorem splice_of_le (C : E →L[ℝ] E) {s : ℝ} (hs : s ≤ -2) : splice A C s = C := by
  simp [splice, max_eq_right (by linarith : s ≤ -1), min_eq_left (by linarith : (1 : ℝ) ≤ -1 - s)]

/-- The coefficient `-B†` of the formal adjoint equation of a continuous family is continuous. -/
private theorem continuous_neg_adjoint [CompleteSpace E] {B : ℝ → E →L[ℝ] E}
    (hB : Continuous B) : Continuous fun s ↦ -ContinuousLinearMap.adjoint (B s) :=
  (ContinuousLinearMap.adjoint.continuous.comp hB).neg

variable [FiniteDimensional ℝ E] {Aplus S : E →L[ℝ] E} {c : ℝ}

/-- The index of the trajectory operator of `splice A (σ • 1)` with `σ = ±1`, computed in two ways:
by the square-integrable solutions of the equation and of its formal adjoint, and by the negative
inertia of the Lyapunov forms `σ • 1` and `S` of its two limits. -/
private theorem finrank_sub_finrank_splice (hA : Continuous A) (hS : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hc : 0 < c) (hplus : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪S (Aplus v), v⟫_ℝ)
    (htop : Tendsto A atTop (𝓝 Aplus)) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    (Module.finrank ℝ (squareIntegrableSolutions (splice A (σ • 1))) : ℤ) -
        Module.finrank ℝ (squareIntegrableSolutions
          fun s ↦ -ContinuousLinearMap.adjoint (splice A (σ • 1) s)) =
      Module.finrank ℝ (Module.End.pointSpectralSubspace (σ • 1 : Module.End ℝ E) (Iio 0)) -
        Module.finrank ℝ (Module.End.pointSpectralSubspace (S : E →ₗ[ℝ] E) (Iio 0)) := by
  have hB := continuous_splice hA (σ • 1)
  have hBbot : Tendsto (splice A (σ • 1)) atBot (𝓝 (σ • 1)) :=
    tendsto_const_nhds.congr' (eventually_atBot.2 ⟨-2, fun s hs ↦ (splice_of_le _ hs).symm⟩)
  have hBtop : Tendsto (splice A (σ • 1)) atTop (𝓝 Aplus) :=
    htop.congr' (eventually_atTop.2 ⟨0, fun s hs ↦ (splice_of_lt _ (by linarith)).symm⟩)
  -- The constant `σ • 1` is its own symmetric Lyapunov form.
  have hσsym : ((σ • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric := by
    rw [ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_one]
    exact LinearMap.IsSymmetric.one.smul (conj_trivial σ)
  have hσform : ∀ v, 1 * ‖v‖ ^ 2 ≤ ⟪(σ • 1 : E →L[ℝ] E) ((σ • 1 : E →L[ℝ] E) v), v⟫_ℝ := by
    rcases hσ with rfl | rfl <;> simp
  set BL := (hB.memLp_top_of_tendsto hBbot hBtop (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))).toLp _
  have hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] splice A (σ • 1) :=
    MemLp.coeFn_toLp _
  rw [← index_trajectoryOperator_eq_finrank_sub_finrank_of_hasLyapunovForm hB
    (ContinuousLinearMap.hasLyapunovForm_iff.2 ⟨_, hσsym, 1, one_pos, hσform⟩)
    (ContinuousLinearMap.hasLyapunovForm_iff.2 ⟨S, hS, c, hc, hplus⟩) hBbot hBtop BL hBL,
    index_trajectoryOperator_eq_finrank_pointSpectralSubspace_sub_finrank_of_forall_le_inner hB
      hσsym hS one_pos hc hσform hplus hBbot hBtop BL hBL,
    ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_one]

/-- **The dimension of the decaying solutions at `+∞`.** Let `A` be a continuous family on a
finite-dimensional real inner product space tending at `+∞` to an operator `A⁺` with a symmetric
Lyapunov form `S`: `c ‖v‖² ≤ ⟪S (A⁺ v), v⟫` with `c > 0`. Then the solutions of `v' + A v = 0`
that are square integrable on `(0, ∞)` form a space of dimension `dim E - n⁻(S)`, where `n⁻(S)`
is the number of negative eigenvalues of `S`. -/
theorem finrank_squareIntegrableSolutionsAtTop_add_finrank_pointSpectralSubspace
    (hA : Continuous A) (hS : (S : E →ₗ[ℝ] E).IsSymmetric) (hc : 0 < c)
    (hplus : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪S (Aplus v), v⟫_ℝ) (htop : Tendsto A atTop (𝓝 Aplus)) :
    Module.finrank ℝ (squareIntegrableSolutionsAtTop A) +
        Module.finrank ℝ (Module.End.pointSpectralSubspace (S : E →ₗ[ℝ] E) (Iio 0)) =
      Module.finrank ℝ E := by
  have h := finrank_sub_finrank_splice hA hS hc hplus htop (σ := -1) (.inr rfl)
  set B := splice A ((-1 : ℝ) • 1) with hBdef
  have hB : Continuous B := continuous_splice hA _
  have hBadj : Continuous fun s ↦ -ContinuousLinearMap.adjoint (B s) := continuous_neg_adjoint hB
  -- At `-∞`, where `B = -1`, every solution of `v' + B v = 0` decays and no solution of the
  -- adjoint equation does.
  have hsol : squareIntegrableSolutions B = squareIntegrableSolutionsAtTop A := by
    rw [squareIntegrableSolutions_eq_inf hB,
      squareIntegrableSolutionsAtBot_eq_top_of_forall_le hB (c := -1) (a := -2) (by norm_num)
        fun s hs ↦ splice_of_le _ hs,
      squareIntegrableSolutionsAtTop_congr hB hA (a := -1) (by norm_num)
        fun s hs ↦ splice_of_lt _ hs, top_inf_eq]
  have hadj : squareIntegrableSolutions (fun s ↦ -ContinuousLinearMap.adjoint (B s)) = ⊥ := by
    rw [squareIntegrableSolutions_eq_inf hBadj,
      squareIntegrableSolutionsAtBot_eq_bot_of_forall_le hBadj (c := 1) (a := -2) one_pos
        fun s hs ↦ by simp [hBdef, splice_of_le _ hs, ContinuousLinearMap.adjoint_one],
      bot_inf_eq]
  have hneg := Module.End.pointSpectralSubspace_smul_one_of_mem (𝕜 := ℝ) (E := E) (μ := -1)
    (Ω := Iio 0) (by norm_num)
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hneg
  rw [hsol, hadj, finrank_bot, Nat.cast_zero, sub_zero, hneg, finrank_top] at h
  omega

/-- **The dimension of the decaying solutions of the adjoint equation at `+∞`.** Let `A` be a
continuous family on a finite-dimensional real inner product space tending at `+∞` to an operator
`A⁺` with a symmetric Lyapunov form `S`: `c ‖v‖² ≤ ⟪S (A⁺ v), v⟫` with `c > 0`. Then the
solutions of the formal adjoint equation `w' = A† w` that are square integrable on `(0, ∞)` form a
space of dimension `n⁻(S)`, the number of negative eigenvalues of `S`. -/
theorem finrank_squareIntegrableSolutionsAtTop_neg_adjoint
    (hA : Continuous A) (hS : (S : E →ₗ[ℝ] E).IsSymmetric) (hc : 0 < c)
    (hplus : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪S (Aplus v), v⟫_ℝ) (htop : Tendsto A atTop (𝓝 Aplus)) :
    Module.finrank ℝ
        (squareIntegrableSolutionsAtTop fun s ↦ -ContinuousLinearMap.adjoint (A s)) =
      Module.finrank ℝ (Module.End.pointSpectralSubspace (S : E →ₗ[ℝ] E) (Iio 0)) := by
  have h := finrank_sub_finrank_splice hA hS hc hplus htop (σ := 1) (.inl rfl)
  set B := splice A ((1 : ℝ) • 1) with hBdef
  have hB : Continuous B := continuous_splice hA _
  have hBadj : Continuous fun s ↦ -ContinuousLinearMap.adjoint (B s) := continuous_neg_adjoint hB
  -- At `-∞`, where `B = 1`, no solution of `v' + B v = 0` decays and every solution of the
  -- adjoint equation does.
  have hsol : squareIntegrableSolutions B = ⊥ := by
    rw [squareIntegrableSolutions_eq_inf hB,
      squareIntegrableSolutionsAtBot_eq_bot_of_forall_le hB (c := 1) (a := -2) one_pos
        fun s hs ↦ splice_of_le _ hs, bot_inf_eq]
  have hadj : squareIntegrableSolutions (fun s ↦ -ContinuousLinearMap.adjoint (B s)) =
      squareIntegrableSolutionsAtTop fun s ↦ -ContinuousLinearMap.adjoint (A s) := by
    rw [squareIntegrableSolutions_eq_inf hBadj,
      squareIntegrableSolutionsAtBot_eq_top_of_forall_le hBadj (c := -1) (a := -2) (by norm_num)
        fun s hs ↦ by simp [hBdef, splice_of_le _ hs, ContinuousLinearMap.adjoint_one],
      squareIntegrableSolutionsAtTop_congr hBadj (continuous_neg_adjoint hA) (a := -1)
        (by norm_num) fun s hs ↦ by simp [hBdef, splice_of_lt _ hs], top_inf_eq]
  have hpos := Module.End.pointSpectralSubspace_smul_one_of_notMem (𝕜 := ℝ) (E := E) (μ := 1)
    (Ω := Iio 0) (by norm_num)
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hpos
  rw [hsol, hadj, finrank_bot, Nat.cast_zero, zero_sub, hpos, finrank_bot] at h
  omega

/-- **The decaying solutions of the adjoint equation at `+∞` are the orthogonal complement.**
For a continuous family `A` on a finite-dimensional real inner product space tending at `+∞` to
an operator with a Lyapunov form, the initial values of the solutions of `w' = A† w` square
integrable on `(0, ∞)` are exactly the vectors orthogonal to the initial values of the solutions
of `v' + A v = 0` square integrable on `(0, ∞)`. -/
theorem squareIntegrableSolutionsAtTop_neg_adjoint_eq_orthogonal (hA : Continuous A)
    (hplus : Aplus.HasLyapunovForm) (htop : Tendsto A atTop (𝓝 Aplus)) :
    (squareIntegrableSolutionsAtTop fun s ↦ -ContinuousLinearMap.adjoint (A s)) =
      (squareIntegrableSolutionsAtTop A)ᗮ := by
  obtain ⟨S, hS, c, hc, hcS⟩ := ContinuousLinearMap.hasLyapunovForm_iff.1 hplus
  refine Submodule.eq_of_le_of_finrank_eq
    (squareIntegrableSolutionsAtTop_neg_le_orthogonal
      fun s x y ↦ (ContinuousLinearMap.adjoint_inner_right (A s) x y).symm) ?_
  have h₁ := finrank_squareIntegrableSolutionsAtTop_add_finrank_pointSpectralSubspace hA hS hc
    hcS htop
  have h₂ := finrank_squareIntegrableSolutionsAtTop_neg_adjoint hA hS hc hcS htop
  have h₃ := (squareIntegrableSolutionsAtTop A).finrank_add_finrank_orthogonal
  omega

/-- **The decaying solutions of the adjoint equation at `-∞` are the orthogonal complement.**
For a continuous family `A` on a finite-dimensional real inner product space tending at `-∞` to
an operator with a Lyapunov form, the initial values of the solutions of `w' = A† w` square
integrable on `(-∞, 0)` are exactly the vectors orthogonal to the initial values of the solutions
of `v' + A v = 0` square integrable on `(-∞, 0)`. -/
theorem squareIntegrableSolutionsAtBot_neg_adjoint_eq_orthogonal {Aminus : E →L[ℝ] E}
    (hA : Continuous A)
    (hminus : Aminus.HasLyapunovForm) (hbot : Tendsto A atBot (𝓝 Aminus)) :
    (squareIntegrableSolutionsAtBot fun s ↦ -ContinuousLinearMap.adjoint (A s)) =
      (squareIntegrableSolutionsAtBot A)ᗮ := by
  -- Reverse time: `A` becomes `s ↦ -A (-s)`, which tends to `-Aminus` at `+∞`.
  have hA' : Continuous fun s ↦ -A (-s) := (hA.comp continuous_neg).neg
  have htop' : Tendsto (fun s ↦ -A (-s)) atTop (𝓝 (-Aminus)) :=
    (hbot.comp tendsto_neg_atTop_atBot).neg
  have h := squareIntegrableSolutionsAtTop_neg_adjoint_eq_orthogonal hA' hminus.neg htop'
  rw [squareIntegrableSolutionsAtBot_eq_atTop, squareIntegrableSolutionsAtBot_eq_atTop, ← h]
  simp

/-- **The cokernel of the trajectory operator.** For a continuous family `A` on a
finite-dimensional real inner product space whose limits at `±∞` have Lyapunov forms, the
square-integrable solutions of the formal adjoint equation `w' = A† w`, which model the cokernel
of `u ↦ u' + A u`, have as initial values the orthogonal complement of the sum of the decaying
solution spaces of `v' + A v = 0` at the two ends. -/
theorem squareIntegrableSolutions_neg_adjoint_eq_orthogonal_sup {Aminus : E →L[ℝ] E}
    (hA : Continuous A)
    (hminus : Aminus.HasLyapunovForm) (hplus : Aplus.HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus)) :
    (squareIntegrableSolutions fun s ↦ -ContinuousLinearMap.adjoint (A s)) =
      (squareIntegrableSolutionsAtBot A ⊔ squareIntegrableSolutionsAtTop A)ᗮ := by
  rw [squareIntegrableSolutions_eq_inf (continuous_neg_adjoint hA),
    squareIntegrableSolutionsAtBot_neg_adjoint_eq_orthogonal hA hminus hbot,
    squareIntegrableSolutionsAtTop_neg_adjoint_eq_orthogonal hA hplus htop,
    Submodule.inf_orthogonal]

/-- **The decaying solutions at `+∞` for an invertible symmetric limit.** For a continuous family
on a finite-dimensional real inner product space tending at `+∞` to a symmetric operator `A⁺`
with `α ‖v‖ ≤ ‖A⁺ v‖`, `α > 0`, the solutions of `v' + A v = 0` square integrable on `(0, ∞)`
form a space of dimension the number of positive eigenvalues of `A⁺`. -/
theorem finrank_squareIntegrableSolutionsAtTop_of_isSymmetric (hA : Continuous A)
    (hsym : (Aplus : E →ₗ[ℝ] E).IsSymmetric) {α : ℝ} (hα : 0 < α)
    (hgap : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖) (htop : Tendsto A atTop (𝓝 Aplus)) :
    Module.finrank ℝ (squareIntegrableSolutionsAtTop A) =
      Module.finrank ℝ (Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Ioi 0)) := by
  have hform : ∀ v, α ^ 2 * ‖v‖ ^ 2 ≤ ⟪Aplus (Aplus v), v⟫_ℝ := fun v ↦ by
    rw [show ⟪Aplus (Aplus v), v⟫_ℝ = ‖Aplus v‖ ^ 2 by
      rw [← real_inner_self_eq_norm_sq, hsym.apply_clm], ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (hgap v) 2
  have h₁ := finrank_squareIntegrableSolutionsAtTop_add_finrank_pointSpectralSubspace hA hsym
    (by positivity) hform htop
  have hker : LinearMap.ker (Aplus : E →ₗ[ℝ] E) = ⊥ := LinearMap.ker_eq_bot.2
    (ContinuousLinearMap.injective_of_forall_norm_le fun v ↦ (le_inv_mul_iff₀ hα).2 (hgap v))
  have h₂ :=
    (Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Ioi 0)).finrank_add_finrank_orthogonal
  rw [hsym.orthogonal_pointSpectralSubspace_Ioi_zero hker] at h₂
  omega

/-- **The decaying solutions at `-∞` for an invertible symmetric limit.** For a continuous family
on a finite-dimensional real inner product space tending at `-∞` to a symmetric operator `A⁻`
with `α ‖v‖ ≤ ‖A⁻ v‖`, `α > 0`, the solutions of `v' + A v = 0` square integrable on `(-∞, 0)`
form a space of dimension the number of negative eigenvalues of `A⁻`. -/
theorem finrank_squareIntegrableSolutionsAtBot_of_isSymmetric {Aminus : E →L[ℝ] E}
    (hA : Continuous A) (hsym : (Aminus : E →ₗ[ℝ] E).IsSymmetric) {α : ℝ} (hα : 0 < α)
    (hgap : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hbot : Tendsto A atBot (𝓝 Aminus)) :
    Module.finrank ℝ (squareIntegrableSolutionsAtBot A) =
      Module.finrank ℝ (Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Iio 0)) := by
  have hA' : Continuous fun s ↦ -A (-s) := (hA.comp continuous_neg).neg
  have htop' : Tendsto (fun s ↦ -A (-s)) atTop (𝓝 (-Aminus)) :=
    (hbot.comp tendsto_neg_atTop_atBot).neg
  rw [squareIntegrableSolutionsAtBot_eq_atTop,
    finrank_squareIntegrableSolutionsAtTop_of_isSymmetric hA'
      (by rw [ContinuousLinearMap.toLinearMap_neg]; exact hsym.neg) hα
      (fun v ↦ by simpa using hgap v) htop',
    ContinuousLinearMap.toLinearMap_neg, Module.End.pointSpectralSubspace_neg, neg_Ioi, neg_zero]

namespace WeakDerivStep

/-- **Surjectivity of the trajectory operator is transversality of the decaying solutions.** Let
`A` be a continuous family of operators on a finite-dimensional real inner product space whose
limits at `±∞` have Lyapunov forms. Then `u ↦ u' + A u` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is onto
exactly when the initial values of the solutions of `v' + A v = 0` square integrable on
`(-∞, 0)` and of those square integrable on `(0, ∞)` together span `E`. -/
theorem surjective_trajectoryOperator_iff_sup_eq_top {Aminus : E →L[ℝ] E} (hA : Continuous A)
    (hminus : Aminus.HasLyapunovForm) (hplus : Aplus.HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    Function.Surjective (trajectoryOperator (p := 2) AL) ↔
      squareIntegrableSolutionsAtBot A ⊔ squareIntegrableSolutionsAtTop A = ⊤ := by
  obtain ⟨BL, hBL⟩ := exists_ae_eq_adjoint AL hAL
  have hneg : -BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ -ContinuousLinearMap.adjoint (A s) := by
    filter_upwards [Lp.coeFn_neg BL, hBL] with s hs hBs
    simp only [hs, Pi.neg_apply, hBs]
  rw [surjective_trajectoryOperator_iff_ker_neg_eq_bot (ae_eq_adjoint_of_ae_eq hAL hBL)
      (isClosed_range_trajectoryOperator_of_hasLyapunovForm hA hminus hplus hbot htop AL hAL),
    ker_trajectoryOperator_eq_bot_iff (continuous_neg_adjoint hA) (-BL) hneg,
    squareIntegrableSolutions_neg_adjoint_eq_orthogonal_sup hA hminus hplus hbot htop,
    Submodule.orthogonal_eq_bot_iff]

end WeakDerivStep

end TauCeti
