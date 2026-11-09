/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LyapunovForm
public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
public import TauCeti.Analysis.ODE.Linear
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Exponential
import TauCeti.Analysis.InnerProductSpace.Spectrum
import TauCeti.Analysis.Normed.Operator.Exponential

/-!
# The inertia of a Lyapunov form

Let `A` be an operator on a finite-dimensional real inner product space `E` with a Lyapunov form:
a symmetric `S` and `c > 0` with `c ‖v‖² ≤ ⟪S (A v), v⟫` for all `v`. Along every solution
`w(t) = exp (t • A) v` of `w' = A w`, the quadratic form `V(w) = ⟪S w, w⟫` increases at rate at
least `2 c ‖w‖²`. The inertia theorem of Ostrowski and Schneider says that `S` then sees the
splitting of `E` into the stable and unstable subspaces of the flow:

* the number of negative eigenvalues of `S`, counted with multiplicity, is the dimension of the
  stable subspace `A.stableSubspace` (`exp (t • A) v → 0` as `t → ∞`);
* the number of positive eigenvalues of `S` is the dimension of the unstable subspace
  `A.unstableSubspace` (`exp (t • A) v → 0` as `t → -∞`);
* the two subspaces are complementary, so `E` is the direct sum of the stable and the unstable
  subspace of every operator with a Lyapunov form.

For a symmetric invertible `A` the form `S = A` gives back the count of the stable directions of
`exp (t • A)` by the negative eigenvalues of `A`. In general the first item turns a count of
negative eigenvalues of a Lyapunov form, the quantity that coercive estimates for the operator
`d/ds + A(s)` on the line naturally produce at the limits `A±`, into the dimension of the stable
subspace of `A±`, which depends on `A±` alone and not on the chosen forms.

The proof is dynamical and does not use the spectral decomposition of `A`. On the stable
subspace `V` tends to `0` along the flow while increasing, so `S` is negative definite there; this
bounds its dimension by the number of negative eigenvalues. Conversely, a vector whose forward
orbit stays in the cone `{V ≤ 0}` lies in the stable subspace, since the increments of `V` over
unit time dominate `‖w‖²` and tend to `0`
(`ContinuousLinearMap.mem_stableSubspace_iff_forall_inner_nonpos`). The cone contains the
negative spectral subspace `N` of `S`, so every vector of `exp (-n • A) N`, a subspace of the same
dimension, has its orbit in the cone up to time `n`. A limit of orthonormal frames of these
subspaces is an orthonormal frame of vectors whose whole forward orbits stay in the cone, which
bounds the dimension of the stable subspace from below.

## Main results

In the namespace `ContinuousLinearMap`, for `S` symmetric with `c ‖v‖² ≤ ⟪S (A v), v⟫`, `c > 0`:

* `inner_apply_self_neg_of_mem_stableSubspace`, `inner_apply_self_pos_of_mem_unstableSubspace`:
  `S` is negative definite on the stable subspace and positive definite on the unstable one.
* `mem_stableSubspace_iff_forall_inner_nonpos`, `mem_unstableSubspace_iff_forall_inner_nonneg`: a
  vector is stable exactly when its forward orbit stays in the cone `{⟪S w, w⟫ ≤ 0}`, and unstable
  exactly when its backward orbit stays in the cone `{⟪S w, w⟫ ≥ 0}`.
* `finrank_stableSubspace_eq_finrank_pointSpectralSubspace_Iio`: the stable dimension is the
  number of negative eigenvalues of `S`.
* `finrank_unstableSubspace_eq_finrank_pointSpectralSubspace_Ioi`: the unstable dimension is the
  number of positive eigenvalues of `S`.
* `HasLyapunovForm.isCompl_stableSubspace_unstableSubspace`: an operator with a Lyapunov form
  splits `E` into its stable and unstable subspaces.

## References

* A. Ostrowski and H. Schneider, *Some theorems on the inertia of general matrices*, J. Math. Anal.
  Appl. **4** (1962), 72–84.
* R. A. Horn and C. R. Johnson, *Topics in Matrix Analysis*, Cambridge University Press, 1991,
  §2.4 (the inertia theorem).
-/

public section

open Filter Module NormedSpace Set Topology
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A S : E →L[ℝ] E} {c : ℝ}

/-! ### The Lyapunov function along the flow -/

/-- The derivative of `t ↦ ⟪S w(t), w(t)⟫` along `w(t) = exp (t • A) v` is `2 ⟪S (A w), w⟫`. -/
private theorem hasDerivAt_inner_exp_smul_apply (hS : (S : E →ₗ[ℝ] E).IsSymmetric) (v : E)
    (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ ⟪S (exp (t • A) v), exp (t • A) v⟫_ℝ)
      (2 * ⟪S (A (exp (t • A) v)), exp (t • A) v⟫_ℝ) t := by
  have hw : HasDerivAt (fun t : ℝ ↦ exp (t • A) v) (A (exp (t • A) v)) t := by
    simpa using (hasDerivAt_exp_smul_const' A t).clm_apply (hasDerivAt_const t v)
  have hSw : HasDerivAt (fun t : ℝ ↦ S (exp (t • A) v)) (S (A (exp (t • A) v))) t :=
    S.hasFDerivAt.comp_hasDerivAt t hw
  convert hSw.inner ℝ hw using 1
  rw [hS.apply_clm, real_inner_comm (A (exp (t • A) v)) (S (exp (t • A) v))]
  ring

/-- The Lyapunov function increases along the flow. -/
private theorem monotone_inner_exp_smul_apply (hS : (S : E →ₗ[ℝ] E).IsSymmetric) (hc : 0 < c)
    (hcS : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪S (A v), v⟫_ℝ) (v : E) :
    Monotone fun t : ℝ ↦ ⟪S (exp (t • A) v), exp (t • A) v⟫_ℝ :=
  monotone_of_hasDerivAt_nonneg (fun t ↦ hasDerivAt_inner_exp_smul_apply hS v t) fun t ↦ by
    have := hcS (exp (t • A) v)
    have : 0 ≤ c * ‖exp (t • A) v‖ ^ 2 := by positivity
    simp only [Pi.zero_apply]
    linarith

/-- Along a nonzero orbit, the Lyapunov function increases strictly. -/
private theorem strictMono_inner_exp_smul_apply (hS : (S : E →ₗ[ℝ] E).IsSymmetric) (hc : 0 < c)
    (hcS : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪S (A v), v⟫_ℝ) {v : E} (hv : v ≠ 0) :
    StrictMono fun t : ℝ ↦ ⟪S (exp (t • A) v), exp (t • A) v⟫_ℝ :=
  strictMono_of_hasDerivAt_pos (fun t ↦ hasDerivAt_inner_exp_smul_apply hS v t) fun t ↦ by
    have hw : exp (t • A) v ≠ 0 := fun h0 ↦ hv <| by
      simpa only [expEquiv_apply, expEquiv_symm_apply, h0, map_zero] using
        ((expEquiv (t • A)).symm_apply_apply v).symm
    have := hcS (exp (t • A) v)
    have : 0 < c * ‖exp (t • A) v‖ ^ 2 := by positivity
    linarith

/-- **Unit-time increments of the Lyapunov function are coercive.** There is `δ > 0` with
`δ ‖v‖² ≤ ⟪S w(1), w(1)⟫ - ⟪S v, v⟫` for `w(1) = exp A v`. The increment is the quadratic form of
the symmetric operator `T† S T - S`, `T = exp A`, which is positive and injective by the strict
monotonicity of the Lyapunov function along nonzero orbits. -/
private theorem exists_pos_forall_mul_norm_sq_le_inner_exp_sub
    (hS : (S : E →ₗ[ℝ] E).IsSymmetric) (hc : 0 < c) (hcS : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪S (A v), v⟫_ℝ) :
    ∃ δ > 0, ∀ v : E, δ * ‖v‖ ^ 2 ≤
      ⟪S (exp ((1 : ℝ) • A) v), exp ((1 : ℝ) • A) v⟫_ℝ - ⟪S v, v⟫_ℝ := by
  set T := exp ((1 : ℝ) • A)
  set Q : E →L[ℝ] E := adjoint T ∘L S ∘L T - S
  have hQ (v : E) : ⟪Q v, v⟫_ℝ = ⟪S (T v), T v⟫_ℝ - ⟪S v, v⟫_ℝ := by
    simp only [Q, sub_apply, comp_apply, inner_sub_left, adjoint_inner_left]
  -- At time `0` the orbit starts at `v`, and at time `1` it is at `T v`.
  have hT0 (v : E) : exp ((0 : ℝ) • A) v = v := by simp
  have hpos : (Q : E →ₗ[ℝ] E).IsPositive := by
    refine ⟨fun x y ↦ ?_, fun x ↦ ?_⟩
    · simp only [coe_coe, Q, sub_apply, comp_apply, inner_sub_left, inner_sub_right,
        adjoint_inner_left, adjoint_inner_right, hS.apply_clm]
    · have h := monotone_inner_exp_smul_apply hS hc hcS x zero_le_one
      simp only [hT0] at h
      rw [coe_coe, RCLike.re_to_real, hQ]
      linarith
  have hker : LinearMap.ker (Q : E →ₗ[ℝ] E) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun x hx ↦ ?_
    by_contra hx0
    have h := strictMono_inner_exp_smul_apply hS hc hcS hx0 zero_lt_one
    simp only [hT0] at h
    have hQx : ⟪Q x, x⟫_ℝ = 0 := by rw [← coe_coe, hx, inner_zero_left]
    rw [hQ] at hQx
    linarith
  obtain ⟨δ, hδ, h⟩ := hpos.exists_pos_mul_norm_sq_le_re_inner hker
  exact ⟨δ, hδ, fun v ↦ by simpa only [coe_coe, RCLike.re_to_real, hQ] using h v⟩

/-- The unit-time increment of the Lyapunov function at an arbitrary time of the orbit. -/
private theorem mul_norm_sq_le_inner_exp_add_one_sub {δ : ℝ}
    (hδ : ∀ v : E, δ * ‖v‖ ^ 2 ≤
      ⟪S (exp ((1 : ℝ) • A) v), exp ((1 : ℝ) • A) v⟫_ℝ - ⟪S v, v⟫_ℝ) (v : E) (t : ℝ) :
    δ * ‖exp (t • A) v‖ ^ 2 ≤ ⟪S (exp ((t + 1) • A) v), exp ((t + 1) • A) v⟫_ℝ -
      ⟪S (exp (t • A) v), exp (t • A) v⟫_ℝ := by
  rw [add_comm t 1, exp_add_smul_apply]
  exact hδ _

/-! ### Definiteness on the stable and unstable subspaces -/

/-- On the stable subspace the Lyapunov form is uniformly negative definite. -/
private theorem exists_pos_forall_inner_le_of_mem_stableSubspace
    (hS : (S : E →ₗ[ℝ] E).IsSymmetric) (hc : 0 < c) (hcS : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪S (A v), v⟫_ℝ) :
    ∃ δ > 0, ∀ v ∈ A.stableSubspace, ⟪S v, v⟫_ℝ ≤ -(δ * ‖v‖ ^ 2) := by
  obtain ⟨δ, hδ, hstep⟩ := exists_pos_forall_mul_norm_sq_le_inner_exp_sub hS hc hcS
  refine ⟨δ, hδ, fun v hv ↦ ?_⟩
  rw [mem_stableSubspace] at hv
  have hlim : Tendsto (fun t : ℝ ↦ ⟪S (exp (t • A) v), exp (t • A) v⟫_ℝ) atTop (𝓝 0) := by
    simpa using (((S.continuous.tendsto 0).comp hv).inner hv : Tendsto _ atTop (𝓝 ⟪S 0, 0⟫_ℝ))
  have hmono := monotone_inner_exp_smul_apply hS hc hcS v
  have h1 : ⟪S (exp ((1 : ℝ) • A) v), exp ((1 : ℝ) • A) v⟫_ℝ ≤ 0 :=
    ge_of_tendsto hlim ((eventually_ge_atTop 1).mono fun t ht ↦ hmono ht)
  linarith [hstep v]

/-- **A Lyapunov form is negative definite on the stable subspace.** -/
theorem inner_apply_self_neg_of_mem_stableSubspace (hS : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hc : 0 < c) (hcS : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪S (A v), v⟫_ℝ) {v : E} (hv : v ∈ A.stableSubspace)
    (hv0 : v ≠ 0) : ⟪S v, v⟫_ℝ < 0 := by
  obtain ⟨δ, hδ, h⟩ := exists_pos_forall_inner_le_of_mem_stableSubspace hS hc hcS
  have : 0 < δ * ‖v‖ ^ 2 := by positivity
  linarith [h v hv]

omit [FiniteDimensional ℝ E] in
/-- If `S` is a Lyapunov form of `A` with constant `c`, then `-S` is one of `-A` with the same
constant: this exchanges the stable and unstable subspaces. -/
private theorem lyapunov_neg (hS : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hcS : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪S (A v), v⟫_ℝ) :
    ((-S : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric ∧ ∀ v, c * ‖v‖ ^ 2 ≤ ⟪(-S) ((-A) v), v⟫_ℝ := by
  refine ⟨?_, fun v ↦ by simpa only [neg_apply, map_neg, neg_neg] using hcS v⟩
  rw [toLinearMap_neg]
  exact hS.neg

/-- **A Lyapunov form is positive definite on the unstable subspace.** -/
theorem inner_apply_self_pos_of_mem_unstableSubspace (hS : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hc : 0 < c) (hcS : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪S (A v), v⟫_ℝ) {v : E}
    (hv : v ∈ A.unstableSubspace) (hv0 : v ≠ 0) : 0 < ⟪S v, v⟫_ℝ := by
  rw [← stableSubspace_neg] at hv
  have := inner_apply_self_neg_of_mem_stableSubspace (lyapunov_neg hS hcS).1 hc
    (lyapunov_neg hS hcS).2 hv hv0
  rwa [neg_apply, inner_neg_left, neg_lt_zero] at this

/-! ### The stable subspace as a cone -/

/-- **The stable vectors are those whose forward orbit stays in the negative cone of a Lyapunov
form.** A vector `v` lies in the stable subspace of `A` exactly when
`⟪S w(t), w(t)⟫ ≤ 0` for all `t ≥ 0`, `w(t) = exp (t • A) v`. -/
theorem mem_stableSubspace_iff_forall_inner_nonpos (hS : (S : E →ₗ[ℝ] E).IsSymmetric) (hc : 0 < c)
    (hcS : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪S (A v), v⟫_ℝ) {v : E} :
    v ∈ A.stableSubspace ↔ ∀ t : ℝ, 0 ≤ t → ⟪S (exp (t • A) v), exp (t • A) v⟫_ℝ ≤ 0 := by
  obtain ⟨δ, hδ, hstep⟩ := exists_pos_forall_mul_norm_sq_le_inner_exp_sub hS hc hcS
  set g : ℝ → ℝ := fun t ↦ ⟪S (exp (t • A) v), exp (t • A) v⟫_ℝ
  have hmono : Monotone g := monotone_inner_exp_smul_apply hS hc hcS v
  constructor
  · -- The stable subspace is invariant, and the form is negative definite on it.
    intro hv t _
    obtain ⟨δ', hδ', h⟩ := exists_pos_forall_inner_le_of_mem_stableSubspace hS hc hcS
    have hwt : exp (t • A) v ∈ A.stableSubspace := by
      rw [← SetLike.mem_coe, coe_stableSubspace] at hv ⊢
      rw [← flow_apply, _root_.Flow.apply_mem_stableSet_iff]
      exact hv
    have : 0 ≤ δ' * ‖exp (t • A) v‖ ^ 2 := by positivity
    linarith [h _ hwt]
  · -- `g` is monotone and bounded above, so its unit-time increments tend to `0`; they
    -- dominate `δ ‖w(t)‖²`.
    intro hv
    have hbdd : BddAbove (range g) := ⟨0, by
      rintro _ ⟨t, rfl⟩
      rcases le_total 0 t with ht | ht
      · exact hv t ht
      · exact (hmono ht).trans (hv 0 le_rfl)⟩
    have hL := tendsto_atTop_ciSup hmono hbdd
    have hinc : Tendsto (fun t ↦ g (t + 1) - g t) atTop (𝓝 0) := by
      simpa using (hL.comp (tendsto_atTop_add_const_right atTop 1 tendsto_id)).sub hL
    have hsq : Tendsto (fun t : ℝ ↦ δ * ‖exp (t • A) v‖ ^ 2) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinc
        (fun t ↦ by positivity) fun t ↦ mul_norm_sq_le_inner_exp_add_one_sub hstep v t
    have hsq' : Tendsto (fun t : ℝ ↦ ‖exp (t • A) v‖ ^ 2) atTop (𝓝 0) := by
      simpa [hδ.ne'] using hsq.const_mul δ⁻¹
    have hnorm : Tendsto (fun t : ℝ ↦ ‖exp (t • A) v‖) atTop (𝓝 0) := by
      simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using
        (Real.continuous_sqrt.tendsto 0).comp hsq'
    exact mem_stableSubspace.2 (tendsto_zero_iff_norm_tendsto_zero.2 hnorm)

/-- **The unstable vectors are those whose backward orbit stays in the positive cone of a
Lyapunov form.** A vector `v` lies in the unstable subspace of `A` exactly when
`0 ≤ ⟪S w(t), w(t)⟫` for all `t ≤ 0`, `w(t) = exp (t • A) v`. -/
theorem mem_unstableSubspace_iff_forall_inner_nonneg (hS : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hc : 0 < c) (hcS : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪S (A v), v⟫_ℝ) {v : E} :
    v ∈ A.unstableSubspace ↔ ∀ t : ℝ, t ≤ 0 → 0 ≤ ⟪S (exp (t • A) v), exp (t • A) v⟫_ℝ := by
  rw [← stableSubspace_neg, mem_stableSubspace_iff_forall_inner_nonpos (lyapunov_neg hS hcS).1 hc
    (lyapunov_neg hS hcS).2]
  have key (t : ℝ) : ⟪(-S) (exp (t • -A) v), exp (t • -A) v⟫_ℝ =
      -⟪S (exp ((-t) • A) v), exp ((-t) • A) v⟫_ℝ := by
    rw [smul_neg, ← neg_smul, neg_apply, inner_neg_left]
  refine ⟨fun h t ht ↦ ?_, fun h t ht ↦ ?_⟩
  · simpa [key] using h (-t) (neg_nonneg.2 ht)
  · simpa [key] using h (-t) (neg_nonpos.2 ht)

/-! ### The inertia theorem -/

/-- The stable subspace has at least as many dimensions as `S` has negative eigenvalues. -/
private theorem finrank_pointSpectralSubspace_Iio_le_finrank_stableSubspace
    (hS : (S : E →ₗ[ℝ] E).IsSymmetric) (hc : 0 < c) (hcS : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪S (A v), v⟫_ℝ) :
    finrank ℝ (Module.End.pointSpectralSubspace (S : E →ₗ[ℝ] E) (Iio 0)) ≤
      finrank ℝ A.stableSubspace := by
  set N := Module.End.pointSpectralSubspace (S : E →ₗ[ℝ] E) (Iio 0)
  set m := finrank ℝ N
  -- The time-`(-n)` image of `N`: its vectors stay in the negative cone up to time `n`.
  set W : ℕ → Submodule ℝ E := fun n ↦
    N.map ((expEquiv ((n : ℝ) • A)).symm.toLinearEquiv : E →ₗ[ℝ] E)
  have hW (n : ℕ) : finrank ℝ (W n) = m := LinearEquiv.finrank_map_eq _ _
  have hcone {n : ℕ} {u : E} (hu : u ∈ W n) {t : ℝ} (ht : t ≤ n) :
      ⟪S (exp (t • A) u), exp (t • A) u⟫_ℝ ≤ 0 := by
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hu
    refine (monotone_inner_exp_smul_apply hS hc hcS _ ht).trans ?_
    have hx' : exp ((n : ℝ) • A) ((expEquiv ((n : ℝ) • A)).symm x) = x := by
      rw [← expEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]
    simp only [LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv, hx']
    -- `S` is negative semidefinite on its negative spectral subspace `N`.
    simpa using hS.re_inner_apply_self_le_of_pointSpectrumIn (a := 0)
      (fun y hy ↦ Module.End.map_pointSpectralSubspace_le (Submodule.mem_map_of_mem hy))
      ((Module.End.pointSpectrumIn_pointSpectralSubspace _ _).mono le_rfl Iio_subset_Iic_self) hx
  -- Orthonormal frames of the `W n` subconverge to an orthonormal frame `f`.
  have hframe (n : ℕ) : ∃ g : Fin m → E, Orthonormal ℝ g ∧ ∀ i, g i ∈ W n := by
    set b := (stdOrthonormalBasis ℝ (W n)).reindex (finCongr (hW n))
    exact ⟨fun i ↦ (b i : E), b.orthonormal.comp_linearIsometry (W n).subtypeₗᵢ, fun i ↦ (b i).2⟩
  choose F hF hFW using hframe
  obtain ⟨f, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : Fin m → E) 1).tendsto_subseq
    (x := F) fun n ↦ by
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      exact fun i ↦ ((hF n).1 i).le
  have hlim' (i : Fin m) : Tendsto (fun n ↦ F (φ n) i) atTop (𝓝 (f i)) :=
    ((continuous_apply i).tendsto f).comp hlim
  have hf : Orthonormal ℝ f := by
    refine orthonormal_iff_ite.2 fun i j ↦ tendsto_nhds_unique ((hlim' i).inner (hlim' j)) ?_
    simp only [orthonormal_iff_ite.1 (hF _), tendsto_const_nhds]
  -- Each vector of the limit frame has its whole forward orbit in the negative cone.
  have hfs (i : Fin m) : f i ∈ A.stableSubspace := by
    refine (mem_stableSubspace_iff_forall_inner_nonpos hS hc hcS).2 fun t _ ↦ ?_
    have hcont : Continuous fun y : E ↦ ⟪S (exp (t • A) y), exp (t • A) y⟫_ℝ := by fun_prop
    refine le_of_tendsto ((hcont.tendsto _).comp (hlim' i)) ?_
    have hφt : ∀ᶠ n in atTop, t ≤ (φ n : ℝ) :=
      (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop).eventually_ge_atTop t
    exact hφt.mono fun n hn ↦ hcone (hFW (φ n) i) hn
  calc m = finrank ℝ (Submodule.span ℝ (range f)) := by
        rw [finrank_span_eq_card hf.linearIndependent, Fintype.card_fin]
    _ ≤ finrank ℝ A.stableSubspace :=
        Submodule.finrank_mono (Submodule.span_le.2 (range_subset_iff.2 hfs))

/-- **The inertia theorem for the stable subspace.** If `S` is symmetric and
`c ‖v‖² ≤ ⟪S (A v), v⟫` with `c > 0`, then the dimension of the stable subspace of `A`, on which
`exp (t • A) v → 0` as `t → ∞`, is the number of negative eigenvalues of `S` counted with
multiplicity. -/
theorem finrank_stableSubspace_eq_finrank_pointSpectralSubspace_Iio
    (hS : (S : E →ₗ[ℝ] E).IsSymmetric) (hc : 0 < c) (hcS : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪S (A v), v⟫_ℝ) :
    finrank ℝ A.stableSubspace =
      finrank ℝ (Module.End.pointSpectralSubspace (S : E →ₗ[ℝ] E) (Iio 0)) := by
  refine le_antisymm ?_ (finrank_pointSpectralSubspace_Iio_le_finrank_stableSubspace hS hc hcS)
  set N := Module.End.pointSpectralSubspace (S : E →ₗ[ℝ] E) (Iio 0)
  -- The stable subspace meets the nonnegative spectral subspace `Nᗮ` of `S` only in `0`.
  have hNc : Nᗮ = Module.End.pointSpectralSubspace (S : E →ₗ[ℝ] E) (Ici 0) := by
    rw [hS.orthogonal_pointSpectralSubspace, compl_Iio]
  have hdisj : A.stableSubspace ⊓ Nᗮ = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun v hv ↦ ?_
    by_contra hv0
    have h₁ := inner_apply_self_neg_of_mem_stableSubspace hS hc hcS hv.1 hv0
    have h₂ : 0 ≤ ⟪S v, v⟫_ℝ := by
      simpa using hS.le_re_inner_apply_self_of_pointSpectrumIn (a := 0)
        (fun y hy ↦ Module.End.map_pointSpectralSubspace_le (Submodule.mem_map_of_mem hy))
        (Module.End.pointSpectrumIn_pointSpectralSubspace _ _) (hNc ▸ hv.2)
    linarith
  have h₁ := Submodule.finrank_sup_add_finrank_inf_eq A.stableSubspace Nᗮ
  have h₂ := Submodule.finrank_le (A.stableSubspace ⊔ Nᗮ)
  have h₃ := N.finrank_add_finrank_orthogonal
  rw [hdisj, finrank_bot] at h₁
  omega

/-- **The inertia theorem for the unstable subspace.** If `S` is symmetric and
`c ‖v‖² ≤ ⟪S (A v), v⟫` with `c > 0`, then the dimension of the unstable subspace of `A`, on which
`exp (t • A) v → 0` as `t → -∞`, is the number of positive eigenvalues of `S` counted with
multiplicity. -/
theorem finrank_unstableSubspace_eq_finrank_pointSpectralSubspace_Ioi
    (hS : (S : E →ₗ[ℝ] E).IsSymmetric) (hc : 0 < c) (hcS : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪S (A v), v⟫_ℝ) :
    finrank ℝ A.unstableSubspace =
      finrank ℝ (Module.End.pointSpectralSubspace (S : E →ₗ[ℝ] E) (Ioi 0)) := by
  rw [← stableSubspace_neg, finrank_stableSubspace_eq_finrank_pointSpectralSubspace_Iio
    (lyapunov_neg hS hcS).1 hc (lyapunov_neg hS hcS).2, toLinearMap_neg,
    Module.End.pointSpectralSubspace_neg, neg_Iio, neg_zero]

/-- **An operator with a Lyapunov form splits the space into its stable and unstable
subspaces.** In finite dimensions, if `A` has a Lyapunov form, then every vector is uniquely the
sum of a vector `v` with `exp (t • A) v → 0` as `t → ∞` and one with `exp (t • A) v → 0` as
`t → -∞`. -/
theorem HasLyapunovForm.isCompl_stableSubspace_unstableSubspace (h : A.HasLyapunovForm) :
    IsCompl A.stableSubspace A.unstableSubspace := by
  obtain ⟨S, hS, c, hc, hcS⟩ := hasLyapunovForm_iff.1 h
  -- `S` is injective, so its negative and positive spectral subspaces are complementary.
  have hker : LinearMap.ker (S : E →ₗ[ℝ] E) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun v hv ↦ ?_
    rw [coe_coe] at hv
    have h := hcS v
    rw [hS.apply_clm, hv, inner_zero_right] at h
    have : ‖v‖ ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg ‖v‖]) (sq_nonneg _)
    simpa using this
  set N := Module.End.pointSpectralSubspace (S : E →ₗ[ℝ] E) (Iio 0)
  have hNc : Nᗮ = Module.End.pointSpectralSubspace (S : E →ₗ[ℝ] E) (Ioi 0) := by
    rw [hS.orthogonal_pointSpectralSubspace, compl_Iio, ← Ioi_insert,
      Module.End.pointSpectralSubspace_insert_zero hker]
  have hdim : finrank ℝ E ≤ finrank ℝ A.stableSubspace + finrank ℝ A.unstableSubspace := by
    rw [finrank_stableSubspace_eq_finrank_pointSpectralSubspace_Iio hS hc hcS,
      finrank_unstableSubspace_eq_finrank_pointSpectralSubspace_Ioi hS hc hcS, ← hNc,
      N.finrank_add_finrank_orthogonal]
  refine (Submodule.isCompl_iff_disjoint _ _ hdim).2 (Submodule.disjoint_def.2 fun v hs hu ↦ ?_)
  by_contra hv0
  have h₁ := inner_apply_self_neg_of_mem_stableSubspace hS hc hcS hs hv0
  have h₂ := inner_apply_self_pos_of_mem_unstableSubspace hS hc hcS hu hv0
  linarith

end ContinuousLinearMap
