/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Finite
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
public import TauCeti.Topology.VectorBundle.SphereBundle.DiscBundle
import TauCeti.Topology.CWComplex.Classical.FiberBundle

/-!
# Weak topology, shifted dimensions, and radial fibre homeomorphisms for disc-sphere CW cells

This file collects the prerequisites for the classical relative CW structure on unit disc-sphere
bundle pairs `(D(E), S(E) ∪ D(E)|_A)` constructed in
`TauCeti.Topology.VectorBundle.SphereBundle.CWComplex`:

* `TauCeti.closed_discBundleProj_preimage`: weak-topology closedness transfer along
  `π_D : D(E) → B` over any classical relative CW complex `(C, D)` in a Hausdorff base;
* `TauCeti.thomCellDimension`: the shifted cell dimension `thomCellDimension r q = q + r` of a
  bundle cell over a base `q`-cell for a rank-`r` real vector bundle;
* `TauCeti.fiberRadialHomeomorph`: the radial homeomorphism `(Fin r → ℝ) ≃ₜ F` sending the
  sup-norm open ball, closed ball, and sphere onto the Euclidean ones of `F` (uniformly including
  `r = 0`).

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §18, Lemma 18.1 (cells of Thom spaces and disc-sphere bundle
  pairs over CW bases).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Chapter 0 and
  §4.D.
-/

public section

noncomputable section

open Bundle Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

/-! ### Weak topology of a unit disc bundle over a relative CW complex -/

section WeakTopology

variable {B : Type u} [TopologicalSpace B] [T2Space B]
  (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (E : B → Type u) [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]

/-- **Weak topology of a unit disc bundle over a relative CW complex.** For a finite-rank continuous
Riemannian bundle `E → B` over a Hausdorff space `B` and a classical relative CW complex `(C, D)` in
`B`, a subset `S ⊆ D(E)|_C` is closed in `D(E)` if and only if its intersections with `D(E)|_K` for
every closed cell `K` of `C` and with `D(E)|_D` are closed. -/
theorem closed_discBundleProj_preimage (C : Set B) {D : Set B} [RelCWComplex C D]
    (S : Set (discBundle F E)) (hS : S ⊆ discBundleProj F E ⁻¹' C) :
    IsClosed S ↔
      (∀ n (j : RelCWComplex.cell C n),
        IsClosed (S ∩ discBundleProj F E ⁻¹' RelCWComplex.closedCell n j)) ∧
      IsClosed (S ∩ discBundleProj F E ⁻¹' D) :=
  have : CompactSpace (closedBall (0 : F) 1) :=
    isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
  RelCWComplex.closed_of_forall_exists_trivialization
    (exists_trivialization_discBundleProj F E) C S hS

end WeakTopology

/-! ### Shifted cell dimension and radial fibre homeomorphism -/

/-- Dimension of the bundle cell of `(D(E), S(E))` lying over a base `q`-cell of a rank-`r` real
vector bundle `E`: base dimension `q` plus fibre rank `r`. -/
def thomCellDimension (r q : ℕ) : ℕ :=
  q + r

@[grind =]
theorem thomCellDimension_def (r q : ℕ) : thomCellDimension r q = q + r :=
  (rfl)

@[simp]
theorem thomCellDimension_zero_left (q : ℕ) : thomCellDimension 0 q = q :=
  (rfl)

@[simp]
theorem thomCellDimension_zero_right (r : ℕ) : thomCellDimension r 0 = r :=
  Nat.zero_add r

@[simp]
theorem thomCellDimension_inj (r q₁ q₂ : ℕ) :
    thomCellDimension r q₁ = thomCellDimension r q₂ ↔ q₁ = q₂ :=
  Nat.add_right_cancel_iff

@[simp]
theorem thomCellDimension_sub (r q : ℕ) : thomCellDimension r q - r = q :=
  Nat.add_sub_cancel q r

theorem le_thomCellDimension (r q : ℕ) : r ≤ thomCellDimension r q :=
  Nat.le_add_left r q

theorem le_thomCellDimension_right (r q : ℕ) : q ≤ thomCellDimension r q :=
  Nat.le_add_right q r

theorem thomCellDimension_injective (r : ℕ) : Function.Injective (thomCellDimension r) :=
  fun _ _ h ↦ Nat.add_right_cancel h

section FiberRadial

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Radial homeomorphism `(Fin r → ℝ) ≃ₜ F` sending the sup-norm unit ball and unit sphere onto the
Euclidean unit ball and unit sphere of `F`: applies
`(EuclideanSpace.equiv (Fin r) ℝ).unitBallHomeomorph.symm` followed by the standard orthonormal
frame `EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] F`. Works uniformly for all `r : ℕ`, including `r = 0`. -/
def fiberRadialHomeomorph {r : ℕ} (hr : Module.finrank ℝ F = r) : (Fin r → ℝ) ≃ₜ F :=
  (EuclideanSpace.equiv (Fin r) ℝ).unitBallHomeomorph.symm.trans
    (((stdOrthonormalBasis ℝ F).reindex (finCongr hr)).repr.symm.toHomeomorph)

variable {F}

/-- Explicit formula for `fiberRadialHomeomorph` in terms of `unitBallHomeomorph` and the standard
orthonormal basis of `F`. -/
theorem fiberRadialHomeomorph_apply {r : ℕ} (hr : Module.finrank ℝ F = r) (w : Fin r → ℝ) :
    fiberRadialHomeomorph F hr w =
      ((stdOrthonormalBasis ℝ F).reindex (finCongr hr)).repr.symm
        ((EuclideanSpace.equiv (Fin r) ℝ).unitBallHomeomorph.symm w) :=
  (rfl)

/-- Explicit formula for `(fiberRadialHomeomorph F hr).symm`. -/
theorem fiberRadialHomeomorph_symm_apply {r : ℕ} (hr : Module.finrank ℝ F = r) (y : F) :
    (fiberRadialHomeomorph F hr).symm y =
      (EuclideanSpace.equiv (Fin r) ℝ).unitBallHomeomorph
        (((stdOrthonormalBasis ℝ F).reindex (finCongr hr)).repr y) :=
  (rfl)

@[simp]
theorem fiberRadialHomeomorph_zero {r : ℕ} (hr : Module.finrank ℝ F = r) :
    fiberRadialHomeomorph F hr 0 = 0 := by
  rw [fiberRadialHomeomorph_apply]
  have h0 : (EuclideanSpace.equiv (Fin r) ℝ).unitBallHomeomorph.symm 0 = 0 := by
    apply (EuclideanSpace.equiv (Fin r) ℝ).unitBallHomeomorph.injective
    rw [Homeomorph.apply_symm_apply, ContinuousLinearEquiv.unitBallHomeomorph_apply,
      map_zero, gaugeRescale_zero]
  rw [h0, map_zero]

@[simp]
theorem fiberRadialHomeomorph_symm_zero {r : ℕ} (hr : Module.finrank ℝ F = r) :
    (fiberRadialHomeomorph F hr).symm 0 = 0 := by
  rw [fiberRadialHomeomorph_symm_apply, map_zero, ContinuousLinearEquiv.unitBallHomeomorph_apply,
    map_zero, gaugeRescale_zero]

private lemma norm_fiberRadialHomeomorph {r : ℕ} (hr : Module.finrank ℝ F = r) (w : Fin r → ℝ) :
    ‖fiberRadialHomeomorph F hr w‖ =
      ‖(EuclideanSpace.equiv (Fin r) ℝ).unitBallHomeomorph.symm w‖ := by
  simp [fiberRadialHomeomorph]

@[simp]
theorem norm_fiberRadialHomeomorph_le_one_iff {r : ℕ} (hr : Module.finrank ℝ F = r)
    {w : Fin r → ℝ} :
    ‖fiberRadialHomeomorph F hr w‖ ≤ 1 ↔ ‖w‖ ≤ 1 := by
  rw [norm_fiberRadialHomeomorph,
    (EuclideanSpace.equiv (Fin r) ℝ).norm_unitBallHomeomorph_symm_le_one_iff]

@[simp]
theorem norm_fiberRadialHomeomorph_lt_one_iff {r : ℕ} (hr : Module.finrank ℝ F = r)
    {w : Fin r → ℝ} :
    ‖fiberRadialHomeomorph F hr w‖ < 1 ↔ ‖w‖ < 1 := by
  rw [norm_fiberRadialHomeomorph,
    (EuclideanSpace.equiv (Fin r) ℝ).norm_unitBallHomeomorph_symm_lt_one_iff]

@[simp]
theorem norm_fiberRadialHomeomorph_eq_one_iff {r : ℕ} (hr : Module.finrank ℝ F = r)
    {w : Fin r → ℝ} :
    ‖fiberRadialHomeomorph F hr w‖ = 1 ↔ ‖w‖ = 1 := by
  rw [norm_fiberRadialHomeomorph,
    (EuclideanSpace.equiv (Fin r) ℝ).norm_unitBallHomeomorph_symm_eq_one_iff]

@[simp]
theorem norm_fiberRadialHomeomorph_symm_le_one_iff {r : ℕ} (hr : Module.finrank ℝ F = r) {y : F} :
    ‖(fiberRadialHomeomorph F hr).symm y‖ ≤ 1 ↔ ‖y‖ ≤ 1 := by
  simpa using (norm_fiberRadialHomeomorph_le_one_iff hr
    (w := (fiberRadialHomeomorph F hr).symm y)).symm

@[simp]
theorem norm_fiberRadialHomeomorph_symm_lt_one_iff {r : ℕ} (hr : Module.finrank ℝ F = r) {y : F} :
    ‖(fiberRadialHomeomorph F hr).symm y‖ < 1 ↔ ‖y‖ < 1 := by
  simpa using (norm_fiberRadialHomeomorph_lt_one_iff hr
    (w := (fiberRadialHomeomorph F hr).symm y)).symm

@[simp]
theorem norm_fiberRadialHomeomorph_symm_eq_one_iff {r : ℕ} (hr : Module.finrank ℝ F = r) {y : F} :
    ‖(fiberRadialHomeomorph F hr).symm y‖ = 1 ↔ ‖y‖ = 1 := by
  simpa using (norm_fiberRadialHomeomorph_eq_one_iff hr
    (w := (fiberRadialHomeomorph F hr).symm y)).symm

@[simp]
theorem image_fiberRadialHomeomorph_closedBall {r : ℕ} (hr : Module.finrank ℝ F = r) :
    fiberRadialHomeomorph F hr '' closedBall 0 1 = closedBall 0 1 := by
  rw [Homeomorph.image_eq_preimage_symm]
  ext y
  simp

@[simp]
theorem image_fiberRadialHomeomorph_ball {r : ℕ} (hr : Module.finrank ℝ F = r) :
    fiberRadialHomeomorph F hr '' ball 0 1 = ball 0 1 := by
  rw [Homeomorph.image_eq_preimage_symm]
  ext y
  simp

@[simp]
theorem image_fiberRadialHomeomorph_sphere {r : ℕ} (hr : Module.finrank ℝ F = r) :
    fiberRadialHomeomorph F hr '' sphere 0 1 = sphere 0 1 := by
  rw [Homeomorph.image_eq_preimage_symm]
  ext y
  simp

end FiberRadial

end TauCeti
