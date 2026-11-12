/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
import TauCeti.Analysis.Complex.HolomorphicFunctions.CompactnessExamples
import TauCeti.Topology.Closure
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The hypotheses of compactness for the weak Cauchy–Riemann equation

The planar compactness theorem for the weak equation `TauCeti.IsWeakCauchyRiemannOn` with the
standard structure `J = i` and `η = 0` (McDuff–Salamon, Theorem B.4.2 and Theorem 4.1.1) asks for
a uniform bound on `du_m` and for the images of compact sets to stay in a fixed compact set; at a
boundary with values in a totally real `L`, it asks for `L` to be closed. This file restates the
examples of `TauCeti.Analysis.Complex.HolomorphicFunctions.CompactnessExamples` in the language
of that theorem: each sequence solves the weak equation, its derivatives are the real Fréchet
derivatives `fderiv ℝ`, and the failing hypothesis is stated in the form the theorem uses.

* Closedness of `L`. On every `U ⊆ ℂ`, in particular on the half-disc, the constant maps
  `1 / (m + 2)` solve the weak equation with boundary values in `L = (0, 1) ⊆ ℝ ⊆ ℂ`, and
  converge uniformly to the solution `0`, whose boundary values leave `L` as soon as `U` meets
  the real axis. For the closed `L = ℝ` the boundary values of the limit stay in `L`.
* The gradient bound. The maps `z ↦ m z` solve the weak equation on every open set, with
  `‖fderiv ℝ (m z)‖ = m`, so no constant bounds their derivatives on `D_{1/2}`; they send
  `D_{1/2}` into `D_{m/2}`, and their images of `D_1` lie in no fixed compact set. The maps
  `z ↦ z / m` solve the weak equation with `‖fderiv ℝ (z / m)‖ ≤ 1` and converge to the solution
  `0` with every real iterated derivative, locally uniformly on `ℂ`.
* The image bound. The constant maps `m` solve the weak equation on every `U`, with derivative
  zero, and their images of any nonempty set lie in no fixed compact set.

The non-convergence of the first and last sequences is
`TauCeti.HolomorphicCompactness.not_tendstoLocallyUniformlyOn_natCast_mul` and
`TauCeti.HolomorphicCompactness.not_tendstoLocallyUniformlyOn_natCast`.

## Main results

* `TauCeti.isWeakCauchyRiemannOn_of_differentiableOn`: a holomorphic map on an open set solves
  the homogeneous weak equation for `J = i`, for every exponent.
* `TauCeti.not_exists_isCompact_forall_mapsTo_of_tendsto_norm_atTop`: a sequence whose values at
  one point of `S` have norms tending to infinity violates every image bound on `S`.
* `TauCeti.HolomorphicCompactness.not_mapsTo_zero_ofReal_image_Ioo`: the closedness witness.
* `TauCeti.HolomorphicCompactness.not_exists_norm_fderiv_natCast_mul_le`: the gradient witness.
* `TauCeti.HolomorphicCompactness.tendstoLocallyUniformly_iteratedFDeriv_div_natCast`: the maps
  `z / m` converge to `0` with every real derivative.
* `TauCeti.HolomorphicCompactness.not_exists_isCompact_forall_mapsTo_natCast`: the image-bound
  witness.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 4.1.1 and Theorem B.4.2.
-/

public section

noncomputable section

open Complex Filter Metric MeasureTheory Set Topology TopologicalSpace

namespace TauCeti

variable {p : ENNReal} {Ω : Opens ℂ} {U : Set ℂ}

/-- **Holomorphic maps are weak solutions.** A holomorphic map on an open set `Ω`, with values
in a complete complex normed space, solves the homogeneous weak equation for the structure
`J = i` with every exponent: its real derivative is complex-linear, so `D(i) = i D(1)` and
`D(1) + i D(i) = 0`. -/
theorem isWeakCauchyRiemannOn_of_differentiableOn {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {w : ℂ → F} (hw : DifferentiableOn ℂ w Ω) :
    IsWeakCauchyRiemannOn p Ω (fun _ _ => I • ContinuousLinearMap.id ℝ F) (fun _ _ => 0) w := by
  refine isWeakCauchyRiemannOn_of_contDiffOn
    ((hw.contDiffOn (n := 1) Ω.isOpen).restrict_scalars ℝ) fun z hz => ?_
  have hd := hw.differentiableAt (Ω.isOpen.mem_nhds hz)
  rw [hd.fderiv_restrictScalars ℝ]
  have hI : fderiv ℂ w z I = I • fderiv ℂ w z 1 := by
    rw [← (fderiv ℂ w z).map_smul, smul_eq_mul, mul_one]
  simp [hI, smul_smul]

/-- **Unbounded values violate every image bound.** If the values of `F m` at a point of `S`
have norms tending to infinity, then no compact set contains `F m '' S` for every `m`. -/
theorem not_exists_isCompact_forall_mapsTo_of_tendsto_norm_atTop {α E : Type*}
    [SeminormedAddCommGroup E] {F : ℕ → α → E} {S : Set α} {z : α} (hz : z ∈ S)
    (hF : Tendsto (fun m ↦ ‖F m z‖) atTop atTop) :
    ¬ ∃ K : Set E, IsCompact K ∧ ∀ m, MapsTo (F m) S K := by
  rintro ⟨K, hK, hFK⟩
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  obtain ⟨m, hm⟩ := (hF.eventually_gt_atTop C).exists
  exact hm.not_ge (hC _ (hFK m hz))

namespace HolomorphicCompactness

local notation "Jᵢ" => fun (_ : ℂ) (_ : ℂ) => I • ContinuousLinearMap.id ℝ ℂ

/-! ### Closedness of the boundary condition -/

/-- The constant maps `1 / (m + 2)` solve the homogeneous weak equation for `J = i` on every
set, in particular on the half-disc. -/
theorem isWeakCauchyRiemannOn_ofReal_inv_add_two (m : ℕ) :
    IsWeakCauchyRiemannOn p U Jᵢ (fun _ _ => 0) (fun _ => (((m + 2 : ℝ)⁻¹ : ℝ) : ℂ)) :=
  isWeakCauchyRiemannOn_const _

/-- The constant maps `1 / (m + 2)` satisfy the boundary condition for `L = (0, 1) ⊆ ℝ ⊆ ℂ` on
every set of boundary points. -/
theorem mapsTo_ofReal_inv_add_two (m : ℕ) (S : Set ℂ) :
    MapsTo (fun _ => (((m + 2 : ℝ)⁻¹ : ℝ) : ℂ)) S (ofReal '' Ioo 0 1) :=
  fun _ _ => ofReal_inv_add_two_mem_image_Ioo m

/-- The limit `0` of the constant maps `1 / (m + 2)` violates the boundary condition for
`L = (0, 1)` on every nonempty set of boundary points, although it solves the weak equation: the
closedness of `L` is needed. -/
theorem not_mapsTo_zero_ofReal_image_Ioo {S : Set ℂ} (hS : S.Nonempty) :
    ¬ MapsTo (fun _ => (0 : ℂ)) S (ofReal '' Ioo 0 1) := fun h =>
  zero_notMem_ofReal_image_Ioo (h hS.some_mem)

/-- For the closed `L = ℝ`, the boundary values of the limit of the constant maps `1 / (m + 2)`
stay in `L`, by the closedness of `L`. -/
theorem mapsTo_zero_range_ofReal (S : Set ℂ) : MapsTo (fun _ => (0 : ℂ)) S (range ofReal) :=
  mapsTo_of_tendsto_of_isClosed (l := atTop) isometry_ofReal.isClosedEmbedding.isClosed_range
    (fun m => (mapsTo_ofReal_inv_add_two m S).mono_right (image_subset_range _ _))
    fun z _ => tendstoUniformly_ofReal_inv_add_two.tendsto_at z

/-! ### The gradient bound -/

/-- The maps `z ↦ c z` solve the homogeneous weak equation for `J = i` on every open set. -/
theorem isWeakCauchyRiemannOn_const_mul (c : ℂ) :
    IsWeakCauchyRiemannOn p Ω Jᵢ (fun _ _ => 0) (fun z => c * z) :=
  isWeakCauchyRiemannOn_of_differentiableOn (differentiable_id.const_mul c).differentiableOn

/-- The real derivative of `z ↦ c z` has norm `‖c‖` everywhere. -/
theorem norm_fderiv_const_mul (c z : ℂ) : ‖fderiv ℝ (fun z : ℂ => c * z) z‖ = ‖c‖ := by
  have h : HasFDerivAt (fun z : ℂ => c * z) (c • ContinuousLinearMap.id ℝ ℂ) z := by
    convert (hasFDerivAt_id (𝕜 := ℝ) z).const_smul c using 1
    ext w
    simp
  rw [h.fderiv, norm_smul, ContinuousLinearMap.norm_id, mul_one]

/-- The real derivatives of `z ↦ m z` admit no uniform bound on `D_{1/2}`, so this sequence of
weak solutions violates the gradient bound of the planar compactness theorem. -/
theorem not_exists_norm_fderiv_natCast_mul_le :
    ¬ ∃ C : ℝ, ∀ m : ℕ, ∀ z ∈ ball (0 : ℂ) (1 / 2), ‖fderiv ℝ (fun z : ℂ => m * z) z‖ ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨m, hm⟩ := exists_nat_gt C
  have := hC m 0 (mem_ball_self (by norm_num))
  rw [norm_fderiv_const_mul, Complex.norm_natCast] at this
  exact hm.not_ge this

/-- The maps `z ↦ m z` send `D_{1/2}` into `D_{m/2}`. -/
theorem mapsTo_natCast_mul_ball {m : ℕ} (hm : 0 < m) :
    MapsTo (fun z : ℂ => m * z) (ball 0 (1 / 2)) (ball 0 (m / 2)) := by
  intro z hz
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_mul, Complex.norm_natCast]
  calc (m : ℝ) * ‖z‖ < m * (1 / 2) := by gcongr
    _ = m / 2 := by ring

/-- The images of `D_1` under the maps `z ↦ m z` lie in no fixed compact set. -/
theorem not_exists_isCompact_forall_mapsTo_natCast_mul :
    ¬ ∃ K : Set ℂ, IsCompact K ∧ ∀ m : ℕ, MapsTo (fun z : ℂ => m * z) (ball 0 1) K := by
  refine not_exists_isCompact_forall_mapsTo_of_tendsto_norm_atTop (F := fun m (z : ℂ) => m * z)
    (z := 1 / 2) (by simp; norm_num) ?_
  simp only [norm_mul, Complex.norm_natCast]
  exact tendsto_natCast_atTop_atTop.atTop_mul_const (by norm_num)

/-- The maps `z ↦ z / m` solve the homogeneous weak equation for `J = i` on every open set. -/
theorem isWeakCauchyRiemannOn_div_natCast (m : ℕ) :
    IsWeakCauchyRiemannOn p Ω Jᵢ (fun _ _ => 0) (fun z => z / m) :=
  isWeakCauchyRiemannOn_of_differentiableOn (differentiable_id.div_const _).differentiableOn

/-- The real derivatives of `z ↦ z / m` have norm at most `1`, so this sequence satisfies the
gradient bound of the planar compactness theorem. -/
theorem norm_fderiv_div_natCast_le_one (m : ℕ) (z : ℂ) :
    ‖fderiv ℝ (fun z : ℂ => z / m) z‖ ≤ 1 := by
  simp_rw [div_eq_inv_mul]
  rw [norm_fderiv_const_mul, norm_inv, Complex.norm_natCast]
  rcases m.eq_zero_or_pos with rfl | hm
  · simp
  · exact inv_le_one_of_one_le₀ (Nat.one_le_cast.2 hm)

/-- The maps `z ↦ z / m` converge to the solution `0` in `C^∞` on compact sets: every real
iterated derivative tends to `0` locally uniformly on `ℂ`. -/
theorem tendstoLocallyUniformly_iteratedFDeriv_div_natCast (k : ℕ) :
    TendstoLocallyUniformly (fun (m : ℕ) ↦ iteratedFDeriv ℝ k (fun z : ℂ ↦ z / m))
      (fun _ ↦ 0) atTop := by
  have hid : Continuous (iteratedFDeriv ℝ k (id : ℂ → ℂ)) :=
    contDiff_id.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have h := tendstoLocallyUniformly_of_forall_continuousAt
    (Φ := fun z (s : ℝ) => s • iteratedFDeriv ℝ k (id : ℂ → ℂ) z) (q := 0)
    (fun _ => (continuous_snd.smul (hid.comp continuous_fst)).continuousAt)
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  simp only [zero_smul] at h
  refine h.congr fun m z => ?_
  have hfun : (fun z : ℂ => z / m) = ((m : ℝ)⁻¹ • id : ℂ → ℂ) := by
    ext w
    simp [div_eq_inv_mul, Complex.real_smul]
  rw [hfun, iteratedFDeriv_const_smul_apply contDiff_id.contDiffAt, Function.comp_apply]

/-! ### The image bound -/

/-- The constant maps `m` solve the homogeneous weak equation for `J = i` on every set. Their
derivatives vanish, so they satisfy the gradient bound with constant `0`. -/
theorem isWeakCauchyRiemannOn_natCast (m : ℕ) :
    IsWeakCauchyRiemannOn p U Jᵢ (fun _ _ => 0) (fun _ => (m : ℂ)) :=
  isWeakCauchyRiemannOn_const _

/-- The images of a nonempty set under the constant maps `m` lie in no fixed compact set, so
this sequence of weak solutions violates the image bound. -/
theorem not_exists_isCompact_forall_mapsTo_natCast {S : Set ℂ} (hS : S.Nonempty) :
    ¬ ∃ K : Set ℂ, IsCompact K ∧ ∀ m : ℕ, MapsTo (fun _ => (m : ℂ)) S K :=
  not_exists_isCompact_forall_mapsTo_of_tendsto_norm_atTop (F := fun m (_ : ℂ) => (m : ℂ))
    hS.some_mem (by simpa using tendsto_natCast_atTop_atTop)

end HolomorphicCompactness

end TauCeti
