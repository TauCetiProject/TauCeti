/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
import TauCeti.Analysis.Calculus.FDeriv.RestrictScalars
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Comparison
import TauCeti.Analysis.Complex.HolomorphicFunctions.CompactnessExamples
import TauCeti.Analysis.Complex.IteratedDeriv
import TauCeti.Topology.Closure
import TauCeti.Topology.Compactness.Normed

/-!
# The hypotheses of compactness for the weak Cauchy–Riemann equation

The planar compactness theorem for the weak equation `TauCeti.IsWeakCauchyRiemannOn` with the
standard structure `J = i` and `η = 0` (McDuff–Salamon, Theorem B.4.2 and Theorem 4.1.1) asks for
a uniform bound on `du_m` and for the images of compact sets to stay in a fixed compact set; at a
boundary with values in a totally real `L`, it asks for `L` to be closed. Without boundary, this
theorem is `TauCeti.exists_subseq_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn_I_smul_id`,
which needs only the image bound, since for `J = i` Cauchy's estimates give the gradient bound.
This file restates the examples of
`TauCeti.Analysis.Complex.HolomorphicFunctions.CompactnessExamples` in the language of that
theorem: each sequence solves the weak equation, its derivatives are the real Fréchet derivatives
`fderiv ℝ`, and the failing hypothesis is stated in the form the theorem uses.

* Closedness of `L`. On every `U ⊆ ℂ`, in particular on the half-disc, the constant maps
  `1 / (m + 2)` solve the weak equation with boundary values in `L = (0, 1) ⊆ ℝ ⊆ ℂ`, and
  converge uniformly to the solution `0`, whose boundary values leave `L` as soon as `U` meets
  the real axis. For the closed `L = ℝ` the boundary values of the limit stay in `L`.
* The gradient bound. The maps `z ↦ m z` solve the weak equation on every open set, with
  `‖fderiv ℝ (m z)‖ = m`, so no constant bounds their derivatives on `D_{1/2}`; they send
  `D_{1/2}` into `D_{m/2}`, and their images of any set containing a nonzero point, such as
  `D_{1/2}` or a compact subset of `D_1`, lie in no fixed compact set. The maps
  `z ↦ z / m` solve the weak equation with `‖fderiv ℝ (z / m)‖ ≤ 1` and converge to the solution
  `0` with every real iterated derivative, locally uniformly on `ℂ`.
* The image bound. The constant maps `m` solve the weak equation on every `U`, with derivative
  zero, and their images of any nonempty set lie in no fixed compact set.

The non-convergence of `z ↦ m z` and of the constants `m` is
`TauCeti.HolomorphicCompactness.not_tendstoLocallyUniformlyOn_natCast_mul` and
`TauCeti.HolomorphicCompactness.not_tendstoLocallyUniformlyOn_natCast`.

## Main results

* `TauCeti.HolomorphicCompactness.not_mapsTo_zero_ofReal_image_Ioo`: the closedness witness.
* `TauCeti.HolomorphicCompactness.not_exists_norm_fderiv_natCast_mul_le`: the gradient witness.
* `TauCeti.HolomorphicCompactness.not_exists_isCompact_forall_mapsTo_natCast_mul`: the maps `m z`
  also violate the image bound.
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
  (differentiable_id.const_mul c).differentiableOn.isWeakCauchyRiemannOn

/-- The real derivatives of `z ↦ m z` admit no uniform bound on any nonempty set, such as
`D_{1/2}`, so this sequence of weak solutions violates the gradient bound of the planar
compactness theorem. -/
theorem not_exists_norm_fderiv_natCast_mul_le {S : Set ℂ} (hS : S.Nonempty) :
    ¬ ∃ C : ℝ, ∀ m : ℕ, ∀ z ∈ S, ‖fderiv ℝ (fun z : ℂ => m * z) z‖ ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨m, hm⟩ := exists_nat_gt C
  have := hC m hS.some hS.some_mem
  rw [(differentiableAt_id.const_mul _).norm_fderiv_restrictScalars_eq_norm_deriv ℝ,
    norm_deriv_natCast_mul] at this
  exact hm.not_ge this

/-- The maps `z ↦ m z` send `D_{1/2}` into `D_{m/2}`. -/
theorem mapsTo_natCast_mul_ball {m : ℕ} (hm : 0 < m) :
    MapsTo (fun z : ℂ => m * z) (ball 0 (1 / 2)) (ball 0 (m / 2)) := by
  intro z hz
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_mul, Complex.norm_natCast]
  calc (m : ℝ) * ‖z‖ < m * (1 / 2) := by gcongr
    _ = m / 2 := by ring

/-- The images under the maps `z ↦ m z` of a set containing a nonzero point, such as `D_{1/2}` or
a compact subset of `D_1`, lie in no fixed compact set, so this sequence also violates the image
bound. -/
theorem not_exists_isCompact_forall_mapsTo_natCast_mul {S : Set ℂ} {z : ℂ} (hz : z ∈ S)
    (hz0 : z ≠ 0) :
    ¬ ∃ K : Set ℂ, IsCompact K ∧ ∀ m : ℕ, MapsTo (fun z : ℂ => m * z) S K := by
  refine not_exists_isCompact_forall_mapsTo_of_tendsto_norm_atTop (l := atTop)
    (u := fun (m : ℕ) (z : ℂ) => m * z) hz ?_
  simp only [norm_mul, Complex.norm_natCast]
  exact tendsto_natCast_atTop_atTop.atTop_mul_const (norm_pos_iff.2 hz0)

/-- The maps `z ↦ z / m` solve the homogeneous weak equation for `J = i` on every open set. -/
theorem isWeakCauchyRiemannOn_div_natCast (m : ℕ) :
    IsWeakCauchyRiemannOn p Ω Jᵢ (fun _ _ => 0) (fun z => z / m) :=
  (differentiable_id.div_const _).differentiableOn.isWeakCauchyRiemannOn

/-- The real derivatives of `z ↦ z / m` have norm at most `1`, so this sequence satisfies the
gradient bound of the planar compactness theorem. -/
theorem norm_fderiv_div_natCast_le_one (m : ℕ) (z : ℂ) :
    ‖fderiv ℝ (fun z : ℂ => z / m) z‖ ≤ 1 := by
  rw [(differentiableAt_id.div_const _).norm_fderiv_restrictScalars_eq_norm_deriv ℝ]
  exact norm_deriv_div_natCast_le_one m z

/-- The maps `z ↦ z / m` converge to the solution `0` in `C^∞` on compact sets: every real
iterated derivative tends to `0` locally uniformly on `ℂ`. -/
theorem tendstoLocallyUniformly_iteratedFDeriv_div_natCast (k : ℕ) :
    TendstoLocallyUniformly (fun (m : ℕ) ↦ iteratedFDeriv ℝ k (fun z : ℂ ↦ z / m))
      (fun _ ↦ 0) atTop := by
  have h := tendstoLocallyUniformly_iteratedDeriv_div_natCast 0
  simp only [iteratedDeriv_zero] at h
  rw [← tendstoLocallyUniformlyOn_univ] at h ⊢
  simpa [Pi.zero_def] using
    h.iteratedFDeriv ℝ (fun m => (differentiable_id.div_const _).differentiableOn) isOpen_univ k

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
  not_exists_isCompact_forall_mapsTo_of_tendsto_norm_atTop (u := fun (m : ℕ) (_ : ℂ) => (m : ℂ))
    hS.some_mem (by simpa using tendsto_natCast_atTop_atTop)

end HolomorphicCompactness

end TauCeti
