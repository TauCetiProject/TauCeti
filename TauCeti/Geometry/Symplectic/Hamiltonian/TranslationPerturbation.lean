/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Flow
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
public import TauCeti.Dynamics.PeriodicPts.FixedPointIndex
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.FDeriv.Comp
import TauCeti.Analysis.Calculus.Sard.EqualDimension
import TauCeti.Dynamics.PeriodicPts.LocalPerturbation
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Making periodic points nondegenerate by Hamiltonian translations

Let `(V, ω)` be a finite-dimensional symplectic vector space, for instance a chart of a surface
with its area form, and let `φ` be a self-map of `V`. A point `x` of period `k` is *nondegenerate*
when the linearized return map `d(φ^[k])_x` does not have `1` as an eigenvalue
(`TauCeti.IsNondegenerateFixedPt`). This file shows that an arbitrarily small Hamiltonian
perturbation `ψ`, supported in a prescribed open set `W`, makes every point `x` of a compact set
`K ⊆ W` with `(φ ∘ ψ)^[k] x = x` a nondegenerate fixed point of `(φ ∘ ψ)^[k]`, provided every
orbit of `φ` starting in `W` leaves `W` until time `k`: `φ^[j] y ∉ W` for `y ∈ W` and `0 < j < k`
(`TauCeti.SymplecticForm.exists_hamiltonianFlow_isNondegenerateFixedPt_iterate`). For `k = 1` the
orbit condition is empty, so the fixed points in `K` become nondegenerate, and therefore finite
(`TauCeti.SymplecticForm.exists_hamiltonianFlow_finite_fixedPoints`).

The perturbation is a localized translation. For a compact `K ⊆ W` and a vector `c`, the
Hamiltonian `H(w) = ω(c, χ(w) w)` with a smooth cutoff `χ`, equal to `1` near a neighbourhood of
`K` and supported in `W`, has Hamiltonian vector field `c` where `χ = 1`. So for small `c` its
time-one map `ψ` agrees near `K` with the translation `w ↦ w + c`, it is the identity near every
point outside `W`, and it moves no point by more than a constant `C` times `‖c‖`
(`TauCeti.SymplecticForm.exists_hamiltonianFlow_eventuallyEq_add`). It is also `C¹`-close to the
identity: the vector field of `H` depends linearly on `c` and is Lipschitz with constant at most
`C ‖c‖`, so the derivative of `ψ` is within `exp (C ‖c‖) - 1` of the identity
(`TauCeti.SymplecticForm.norm_fderiv_hamiltonianFlow_sub_id_le`). Since `ψ` is a Hamiltonian
time map it preserves `ω` (`TauCeti.SymplecticForm.apply_fderiv_hamiltonianFlow`), so `φ ∘ ψ` is
symplectic whenever `φ` is.

The choice of `c` is Sard's lemma. Near a point `x ∈ K` the `k`-th iterate of `φ ∘ ψ` is
`w ↦ φ^[k] (w + c)`, because `ψ` is the identity near the later points of the orbit of `x + c`
(`Function.iterate_comp_eventuallyEq_iterate_comp`). So `x` has period `k` exactly when
`y = x + c` solves `g(y) = c` for `g(y) = y - φ^[k](y)`, and `x` is nondegenerate exactly when
the derivative `1 - d(φ^[k])_y` of `g` at `y` is invertible. The critical values of `g` have
measure zero, so its regular values are dense (`TauCeti.dense_setOf_forall_surjective_fderiv`):
arbitrarily small regular values `c` exist, and for them every such `x` is nondegenerate.

This is meant as the transversality step for making all periodic points of an area-preserving
surface map of period at most a cutoff nondegenerate. The orbit condition holds near a point of
least period `k` once `W` is a small enough ball. The perturbations are arbitrarily small in
`C¹`, not only in `C⁰`, so they can be combined with the stability of nondegeneracy under small
`C¹` perturbations (`IsCompact.exists_pos_forall_mem_Icc_isNondegenerateFixedPt_iterate`):
finitely many such steps make the points of period `k` away from the points of smaller period
nondegenerate, and the localized twists of
`TauCeti.Geometry.Symplectic.Hamiltonian.ReturnMapPerturbation` then make the resulting finitely
many orbits nondegenerate in all iterates. That induction over the periods is not carried out
here.

The perturbation also counts degenerate periodic points. If the points of period `k` of `φ` in an
open set `U ⊆ W` form a compact set, possibly degenerate, then near that set the perturbed map has
finitely many points of period `k`, all nondegenerate, and their signed count
`∑ sign det (1 - d((φ ∘ ψ)^[k])_x)` is the fixed-point index of `φ^[k]` on `U`
(`TauCeti.SymplecticForm.exists_hamiltonianFlow_sum_sign_det_eq_fixedPointIndex`). Every other
small perturbation of this kind gives the same count
(`TauCeti.exists_pos_forall_sum_sign_det_iterate_comp_eq_fixedPointIndex`).

## Main results

* `TauCeti.SymplecticForm.exists_hamiltonianFlow_eventuallyEq_add`: localized Hamiltonian
  translations.
* `TauCeti.SymplecticForm.exists_hamiltonianFlow_isNondegenerateFixedPt_iterate`: if every orbit
  starting in `W` leaves `W` until time `k`, an arbitrarily small Hamiltonian translation localized
  in `W` makes the points of period `k` of the perturbed map in a compact set `K ⊆ W`
  nondegenerate.
* `TauCeti.SymplecticForm.exists_hamiltonianFlow_finite_fixedPoints`: the case `k = 1`, in which
  the fixed points in the compact set become nondegenerate and finite.
* `TauCeti.SymplecticForm.exists_hamiltonianFlow_sum_sign_det_eq_fixedPointIndex`: such a
  perturbation of a map with a compact, possibly degenerate, set of points of period `k` has
  nondegenerate periodic points near that set, whose signed count is the fixed-point index.

## References

* R. C. Robinson, *Generic properties of conservative systems*, Amer. J. Math. 92 (1970),
  562–603, for the local perturbations making periodic points of conservative maps
  nondegenerate.
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818–893, for the role of nondegenerate periodic orbits.
-/

public section

noncomputable section

namespace TauCeti.SymplecticForm

open Filter Function Metric MeasureTheory Set Topology
open scoped Manifold NNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V)

/-- If the Hamiltonian vector field is the constant `c` on the `2r`-neighbourhood of `K` and
`‖c‖ < r`, the time-one map agrees near every point of `K` with the translation by `c`. -/
private theorem hamiltonianFlow_eventuallyEq_add_of_forall {H : V → ℝ} {L : ℝ≥0}
    (hX : LipschitzWith L (ω.hamiltonianVectorField H)) {K : Set V} {r : ℝ} {c : V}
    (hfield : ∀ z ∈ thickening (r + r) K, ω.hamiltonianVectorField H z = c) (hc : ‖c‖ < r)
    {x : V} (hx : x ∈ K) : ω.hamiltonianFlow H hX 1 =ᶠ[𝓝 x] fun w ↦ w + c := by
  filter_upwards [isOpen_thickening.mem_nhds
    (self_subset_thickening ((norm_nonneg c).trans_lt hc) K hx)] with x' hx'
  -- The segment from `x'` to `x' + c` stays where the field is `c`.
  refine (ω.hamiltonianFlow_apply_eq_add_smul H hX fun τ hτ ↦ hfield _ ?_).trans (by simp)
  rw [uIcc_of_le zero_le_one] at hτ
  refine thickening_thickening_subset r r K (ball_subset_thickening hx' r ?_)
  simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hτ.1]
  exact (mul_le_of_le_one_left (norm_nonneg c) hτ.2).trans_lt hc

/-- The Hamiltonian `w ↦ ω(c, F(w))` has vector field `B⁻¹ (ω(c, ·) ∘ dF)`, where `B` is `ω` seen
as a continuous map from `V` to its dual. -/
private theorem hamiltonianVectorField_comp_apply {F : V → V} {z : V}
    (hF : DifferentiableAt ℝ F z) (c : V) :
    ω.hamiltonianVectorField (fun w ↦ ω.toBilinForm.toContinuousBilinearMap c (F w)) z =
      ω.toBilinForm.toContinuousBilinearMap.inverse
        ((ω.toBilinForm.toContinuousBilinearMap c).comp (fderiv ℝ F z)) := by
  set B := ω.toBilinForm.toContinuousBilinearMap
  have hd : HasFDerivAt (fun w ↦ B c (F w)) ((B c).comp (fderiv ℝ F z)) z :=
    (B c).hasFDerivAt.comp z hF.hasFDerivAt
  rw [hamiltonianVectorField_def, hd.fderiv]

/-- The operator-norm estimate for the vector field of `hamiltonianVectorField_comp_apply`, with an
arbitrary operator `T` in place of `dF`. -/
private theorem norm_inverse_comp_le (c : V) (T : V →L[ℝ] V) :
    ‖ω.toBilinForm.toContinuousBilinearMap.inverse
        ((ω.toBilinForm.toContinuousBilinearMap c).comp T)‖ ≤
      ‖ω.toBilinForm.toContinuousBilinearMap.inverse‖ * ‖ω.toBilinForm.toContinuousBilinearMap‖ *
        (‖c‖ * ‖T‖) := by
  set B := ω.toBilinForm.toContinuousBilinearMap
  rw [mul_assoc]
  refine (B.inverse.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  calc ‖(B c).comp T‖ ≤ ‖B c‖ * ‖T‖ := (B c).opNorm_comp_le _
    _ ≤ ‖B‖ * ‖c‖ * ‖T‖ := by gcongr; exact B.le_opNorm c
    _ = ‖B‖ * (‖c‖ * ‖T‖) := mul_assoc _ _ _

/-- The Hamiltonian `w ↦ ω(c, F(w))` has vector field bounded by a constant, depending only on
`ω`, times `‖c‖ ‖dF‖`. -/
private theorem norm_hamiltonianVectorField_comp_le {F : V → V} {z : V}
    (hF : DifferentiableAt ℝ F z) (c : V) :
    ‖ω.hamiltonianVectorField (fun w ↦ ω.toBilinForm.toContinuousBilinearMap c (F w)) z‖ ≤
      ‖ω.toBilinForm.toContinuousBilinearMap.inverse‖ * ‖ω.toBilinForm.toContinuousBilinearMap‖ *
        (‖c‖ * ‖fderiv ℝ F z‖) := by
  rw [hamiltonianVectorField_comp_apply ω hF]
  exact norm_inverse_comp_le ω c _

/-- The Hamiltonian `w ↦ ω(c, F(w))` has a Lipschitz vector field, with constant a constant
depending only on `ω`, times `‖c‖` and a Lipschitz constant of `dF`. -/
private theorem lipschitzWith_hamiltonianVectorField_comp {F : V → V} (hF : Differentiable ℝ F)
    {M : ℝ≥0} (hM : LipschitzWith M (fderiv ℝ F)) (c : V) :
    LipschitzWith (‖ω.toBilinForm.toContinuousBilinearMap.inverse‖₊ *
        ‖ω.toBilinForm.toContinuousBilinearMap‖₊ * ‖c‖₊ * M)
      (ω.hamiltonianVectorField fun w ↦ ω.toBilinForm.toContinuousBilinearMap c (F w)) := by
  refine LipschitzWith.of_dist_le_mul fun z z' ↦ ?_
  rw [hamiltonianVectorField_comp_apply ω (hF z), hamiltonianVectorField_comp_apply ω (hF z'),
    dist_eq_norm, ← map_sub, ← ContinuousLinearMap.comp_sub]
  refine (norm_inverse_comp_le ω c _).trans ?_
  rw [← dist_eq_norm]
  grw [hM.dist_le_mul z z']
  push_cast
  exact le_of_eq (by ring)

/-- **Localized Hamiltonian translations.** Let `K` be a compact subset of an open set `W` of a
finite-dimensional symplectic vector space. There are `δ > 0` and `C` such that every vector `c`
gives a smooth Hamiltonian `H`, with compact support inside `W`, whose time-one map `ψ` agrees
near every point of `K` with the translation `w ↦ w + c` when `‖c‖ < δ`, is the identity near
every point outside `W`, moves no point by more than `C ‖c‖`, and has derivative within
`exp (C ‖c‖) - 1` of the identity everywhere. So `ψ` tends to the identity in `C¹` as `c → 0`. The
conclusions hold for every Lipschitz constant of the Hamiltonian vector field, one of which
exists.

The Hamiltonian is `H(w) = ω(c, χ(w) w)` for a smooth cutoff `χ` equal to `1` near `K`, so that
`H = ω(c, ·)` and the Hamiltonian vector field is `c` where `χ = 1`. -/
theorem exists_hamiltonianFlow_eventuallyEq_add {K W : Set V} (hK : IsCompact K) (hW : IsOpen W)
    (hKW : K ⊆ W) :
    ∃ δ > 0, ∃ C, ∀ c : V, ∃ H : V → ℝ, ContDiff ℝ (⊤ : ℕ∞) H ∧ HasCompactSupport H ∧
      tsupport H ⊆ W ∧ (∃ L, LipschitzWith L (ω.hamiltonianVectorField H)) ∧
      ∀ {L : ℝ≥0} (hX : LipschitzWith L (ω.hamiltonianVectorField H)),
        (‖c‖ < δ → ∀ x ∈ K, ω.hamiltonianFlow H hX 1 =ᶠ[𝓝 x] fun w ↦ w + c) ∧
        (∀ w ∉ W, ω.hamiltonianFlow H hX 1 =ᶠ[𝓝 w] id) ∧
        (∀ w, ‖ω.hamiltonianFlow H hX 1 w - w‖ ≤ C * ‖c‖) ∧
        ∀ w, ‖fderiv ℝ (ω.hamiltonianFlow H hX 1) w - ContinuousLinearMap.id ℝ V‖ ≤
          Real.exp (C * ‖c‖) - 1 := by
  obtain ⟨ρ, hρ, hρW⟩ := hK.exists_cthickening_subset_open hW hKW
  -- A smooth cutoff `χ`, equal to `1` on the `2ρ/3`-neighbourhood of `K` and supported in `W`.
  obtain ⟨χ, hχ, -, hχ1, hχc, hχW⟩ := (hK.cthickening (r := ρ / 3 + ρ / 3)).exists_contDiff_cutoff
    hW ((cthickening_mono (by linarith) K).trans hρW)
  -- The field `F(w) = χ(w) w` has a bounded derivative.
  set F : V → V := fun w ↦ χ w • w
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := hχ.smul contDiff_id
  obtain ⟨M, hM⟩ := (hF.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hχc.smul_right.fderiv (𝕜 := ℝ))
  -- `dF` is Lipschitz, being smooth with compact support.
  obtain ⟨M₂, hM₂⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (f := fderiv ℝ F)
    (hχc.smul_right.fderiv (𝕜 := ℝ)) (hF.fderiv_right (m := 1) (by simp)) one_ne_zero
  set B := ω.toBilinForm.toContinuousBilinearMap
  refine ⟨ρ / 3, by positivity, ‖B.inverse‖ * ‖B‖ * max M M₂, fun c ↦ ?_⟩
  set H : V → ℝ := fun w ↦ B c (F w)
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := (B c).contDiff.comp hF
  have hHχ : support H ⊆ support χ := fun w hw h ↦ hw (by simp [H, F, h])
  have hHW : tsupport H ⊆ W := (closure_mono hHχ).trans hχW
  have hHc : HasCompactSupport H := hχc.mono hHχ
  refine ⟨H, hH, hHc, hHW, ω.exists_lipschitzWith_hamiltonianVectorField (hH.of_le (by simp)) hHc,
    fun hX ↦ ⟨fun hc x hx ↦ ω.hamiltonianFlow_eventuallyEq_add_of_forall hX (fun z hz ↦ ?_) hc hx,
      fun w hw ↦ ω.hamiltonianFlow_eventuallyEq_id_of_notMem_tsupport H hX (fun h ↦ hw (hHW h)) 1,
      fun w ↦ ?_, fun w ↦ ?_⟩⟩
  · -- Near `K` the Hamiltonian is the linear function `ω(c, ·)`, whose field is `c`.
    have hev : H =ᶠ[𝓝 z] fun y ↦ ω c y := by
      filter_upwards [isOpen_thickening.mem_nhds hz] with y hy
      have : χ y = 1 := interior_subset (hχ1 (thickening_subset_cthickening _ _ hy))
      simp [H, F, B, this]
    rw [ω.hamiltonianVectorField_congr_of_eventuallyEq hev, hamiltonianVectorField_apply_left]
  · -- The field is bounded by `‖B⁻¹‖ ‖B‖ M ‖c‖`, which bounds the displacement at time one.
    have hbound (z : V) : ‖ω.hamiltonianVectorField H z‖ ≤ ‖B.inverse‖ * ‖B‖ * max M M₂ * ‖c‖ :=
      (ω.norm_hamiltonianVectorField_comp_le (hF.differentiable (by simp) z) c).trans
        (by rw [mul_comm ‖c‖, ← mul_assoc]; gcongr; exact (hM z).trans (le_max_left _ _))
    simpa using ω.norm_hamiltonianFlow_sub_le H hX hbound 1 w
  · -- The field is `‖B⁻¹‖ ‖B‖ M₂ ‖c‖`-Lipschitz, which bounds the derivative of the time-one map.
    have hXc := ω.lipschitzWith_hamiltonianVectorField_comp (hF.differentiable (by simp)) hM₂ c
    rw [ω.hamiltonianFlow_congr H hX hXc]
    refine (ω.norm_fderiv_hamiltonianFlow_sub_id_le H hXc (hH.of_le (by simp)) 1 w).trans
      (sub_le_sub_right (Real.exp_le_exp.2 ?_) 1)
    rw [abs_one, mul_one]
    push_cast
    rw [mul_right_comm]
    gcongr
    exact le_max_right _ _

/-- **Hamiltonian translations make the periodic points through a compact set nondegenerate.**
Let `K` be a compact subset of an open set `W` of a finite-dimensional symplectic vector space,
let `k > 0`, and let `φ` be a self-map that is differentiable along the first `k` points of the
orbit of every point of `W`, and whose orbits starting in `W` leave `W` until time `k`:
`φ^[j] y ∉ W` for `y ∈ W` and `0 < j < k`. For every `ε > 0` there is a smooth Hamiltonian `H`
with compact support inside `W` whose time-one map `ψ` maps `K` into `W`, is the identity near
every point outside `W`, moves no point by more than `ε`, has derivative within `ε` of the identity
everywhere, and makes every point `x ∈ K` with
`(φ ∘ ψ)^[k] x = x` a nondegenerate fixed point of `(φ ∘ ψ)^[k]`. The conclusions hold for every
Lipschitz constant of the Hamiltonian vector field, one of which exists. -/
theorem exists_hamiltonianFlow_isNondegenerateFixedPt_iterate {φ : V → V} {k : ℕ} (hk : 0 < k)
    {K W : Set V} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hφ : ∀ y ∈ W, ∀ j < k, DifferentiableAt ℝ φ (φ^[j] y))
    (hret : ∀ y ∈ W, ∀ j, 0 < j → j < k → φ^[j] y ∉ W) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : V → ℝ, ContDiff ℝ (⊤ : ℕ∞) H ∧ HasCompactSupport H ∧ tsupport H ⊆ W ∧
      (∃ L, LipschitzWith L (ω.hamiltonianVectorField H)) ∧
      ∀ {L : ℝ≥0} (hX : LipschitzWith L (ω.hamiltonianVectorField H)),
        MapsTo (ω.hamiltonianFlow H hX 1) K W ∧
        (∀ w ∉ W, ω.hamiltonianFlow H hX 1 =ᶠ[𝓝 w] id) ∧
        (∀ w, ‖ω.hamiltonianFlow H hX 1 w - w‖ ≤ ε) ∧
        (∀ w, ‖fderiv ℝ (ω.hamiltonianFlow H hX 1) w - ContinuousLinearMap.id ℝ V‖ ≤ ε) ∧
        ∀ x ∈ K, (φ ∘ ω.hamiltonianFlow H hX 1)^[k] x = x →
          IsNondegenerateFixedPt 𝓘(ℝ, V) (φ ∘ ω.hamiltonianFlow H hX 1)^[k] x := by
  obtain ⟨δ, hδ, C, htr⟩ := ω.exists_hamiltonianFlow_eventuallyEq_add hK hW hKW
  obtain ⟨ρ, hρ, hρW⟩ := hK.exists_cthickening_subset_open hW hKW
  -- The regular values of `g(y) = y - φ^[k](y)` on `W` are dense; choose a small one, `c`.
  set g : V → V := fun y ↦ y - φ^[k] y
  have hg (y : V) (hy : y ∈ W) : HasFDerivAt g (ContinuousLinearMap.id ℝ V - fderiv ℝ φ^[k] y) y :=
    (hasFDerivAt_id y).sub (differentiableAt_iterate (hφ y hy)).hasFDerivAt
  borelize V
  -- Translations by vectors of norm below `η` make the displacement and derivative bounds
  -- smaller than `ε`.
  obtain ⟨η, hη, hηε⟩ := Metric.eventually_nhds_iff.1
    ((ContinuousAt.eventually_lt (f := fun x : ℝ ↦ C * x) (g := fun _ ↦ ε) (x₀ := 0)
      (by fun_prop) continuousAt_const (by simpa using hε)).and
    (ContinuousAt.eventually_lt (f := fun x : ℝ ↦ Real.exp (C * x) - 1) (g := fun _ ↦ ε)
      (x₀ := 0) (by fun_prop) continuousAt_const (by simpa using hε)))
  have hr : 0 < min (min δ ρ) η := by positivity
  obtain ⟨c, hcS, hc⟩ := (dense_setOf_forall_surjective_fderiv
    (fun y hy ↦ (hg y hy).differentiableAt) rfl).exists_mem_open isOpen_ball ⟨0, mem_ball_self hr⟩
  obtain ⟨⟨hcδ, hcρ⟩, hcη⟩ : (‖c‖ < δ ∧ ‖c‖ < ρ) ∧ ‖c‖ < η := by
    simpa only [mem_ball_zero_iff, lt_min_iff] using hc
  obtain ⟨hcε, hcε'⟩ := hηε (y := ‖c‖) (by simpa using hcη)
  obtain ⟨H, hH, hHc, hHW, hHX, hψ⟩ := htr c
  refine ⟨H, hH, hHc, hHW, hHX, fun hX ↦ ?_⟩
  obtain ⟨hadd, hid, hdisp, hderiv⟩ := hψ hX
  set ψ := ω.hamiltonianFlow H hX 1
  -- `ψ` translates each point of `K` by `c`, into `W`.
  have hψK (x : V) (hx : x ∈ K) : ψ x = x + c := (hadd hcδ x hx).eq_of_nhds
  have hKc (x : V) (hx : x ∈ K) : x + c ∈ W :=
    hρW (mem_cthickening_of_dist_le _ x ρ K hx (by simpa using hcρ.le))
  refine ⟨fun x hx ↦ (hψK x hx).symm ▸ hKc x hx, hid, fun w ↦ (hdisp w).trans hcε.le,
    fun w ↦ (hderiv w).trans hcε'.le, fun x hx hfix ↦ ?_⟩
  set y := x + c
  have hy : y ∈ W := hKc x hx
  -- Near `x`, the `k`-th iterate of `φ ∘ ψ` is `w ↦ φ^[k] (w + c)`.
  have hev : (φ ∘ ψ)^[k] =ᶠ[𝓝 x] fun w ↦ φ^[k] (w + c) :=
    iterate_comp_eventuallyEq_comp_add hk (hadd hcδ x hx)
      (fun j hj ↦ (hφ y hy j hj).continuousAt) fun j hj hjk ↦ hid _ (hret y hy j hj hjk)
  have hD : HasFDerivAt (φ ∘ ψ)^[k] (fderiv ℝ φ^[k] y) x := by
    have h := (differentiableAt_iterate (hφ y hy)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).add_const c)
    rw [ContinuousLinearMap.comp_id] at h
    exact h.congr_of_eventuallyEq hev
  -- The point `y` solves `g(y) = c`, a regular value, so `1 - d(φ^[k])_y` is injective.
  have hgy : g y = c := by
    have h := hev.eq_of_nhds
    simp only [hfix] at h
    simp [g, y, ← h]
  have hsurj := hcS y hy hgy
  rw [(hg y hy).fderiv] at hsurj
  exact (hD.isNondegenerateFixedPt_iff_injective_id_sub hfix).2 ((LinearMap.injective_iff_surjective
    (f := (ContinuousLinearMap.id ℝ V - fderiv ℝ φ^[k] y : V →ₗ[ℝ] V))).2 hsurj)

/-- **Hamiltonian translations make the fixed points in a compact set nondegenerate.** Let `K` be
a compact subset of an open set `W` of a finite-dimensional symplectic vector space, and let `φ`
be a self-map that is differentiable on `W`. For every `ε > 0` there is a smooth Hamiltonian `H`
with compact support inside `W` whose time-one map `ψ` is the identity near every point outside
`W`, moves no point by more than `ε`, has derivative within `ε` of the identity everywhere, and
makes every fixed point of `φ ∘ ψ` in `K` nondegenerate. In particular `φ ∘ ψ` has only finitely
many fixed points in `K`. The conclusions hold for every Lipschitz constant of the Hamiltonian
vector field, one of which exists. -/
theorem exists_hamiltonianFlow_finite_fixedPoints {φ : V → V} {K W : Set V} (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W) (hφ : ∀ y ∈ W, DifferentiableAt ℝ φ y) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : V → ℝ, ContDiff ℝ (⊤ : ℕ∞) H ∧ HasCompactSupport H ∧ tsupport H ⊆ W ∧
      (∃ L, LipschitzWith L (ω.hamiltonianVectorField H)) ∧
      ∀ {L : ℝ≥0} (hX : LipschitzWith L (ω.hamiltonianVectorField H)),
        (∀ w ∉ W, ω.hamiltonianFlow H hX 1 =ᶠ[𝓝 w] id) ∧
        (∀ w, ‖ω.hamiltonianFlow H hX 1 w - w‖ ≤ ε) ∧
        (∀ w, ‖fderiv ℝ (ω.hamiltonianFlow H hX 1) w - ContinuousLinearMap.id ℝ V‖ ≤ ε) ∧
        (∀ x ∈ K, IsFixedPt (φ ∘ ω.hamiltonianFlow H hX 1) x →
          IsNondegenerateFixedPt 𝓘(ℝ, V) (φ ∘ ω.hamiltonianFlow H hX 1) x) ∧
        (K ∩ fixedPoints (φ ∘ ω.hamiltonianFlow H hX 1)).Finite := by
  obtain ⟨H, hH, hHc, hHW, hHX, hψ⟩ := ω.exists_hamiltonianFlow_isNondegenerateFixedPt_iterate
    one_pos hK hW hKW (fun y hy j hj ↦ by simpa [Nat.lt_one_iff.1 hj] using hφ y hy)
    (fun _ _ j hj hj1 ↦ absurd hj1 (by omega)) hε
  refine ⟨H, hH, hHc, hHW, hHX, fun hX ↦ ?_⟩
  obtain ⟨hmaps, hid, hdisp, hderiv, hnd⟩ := hψ hX
  set ψ := ω.hamiltonianFlow H hX 1
  have hnd' (x : V) (hx : x ∈ K) (hfix : IsFixedPt (φ ∘ ψ) x) :
      IsNondegenerateFixedPt 𝓘(ℝ, V) (φ ∘ ψ) x := by
    simpa using hnd x hx hfix
  refine ⟨hid, hdisp, hderiv, hnd', ?_⟩
  -- The fixed points in `K` form a compact set, since `φ ∘ ψ` is continuous on `K`.
  have hcont : ContinuousOn (fun x ↦ (φ ∘ ψ) x - x) K := by
    intro x hx
    have hψc : Continuous ψ :=
      (ω.contDiff_hamiltonianFlow_apply H 0 hX (hH.of_le (by simp)) 1).continuous
    exact (((hφ _ (hmaps hx)).continuousAt.comp hψc.continuousAt).sub
      continuousAt_id).continuousWithinAt
  have hclosed : IsClosed (K ∩ (fun x ↦ (φ ∘ ψ) x - x) ⁻¹' {0}) :=
    hcont.preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton
  have heq : K ∩ fixedPoints (φ ∘ ψ) = K ∩ (fun x ↦ (φ ∘ ψ) x - x) ⁻¹' {0} := by
    ext x
    simp [IsFixedPt, sub_eq_zero]
  rw [heq]
  refine (hK.of_isClosed_subset hclosed inter_subset_left).finite_of_isNondegenerateFixedPt
    fun x hx ↦ hnd' x hx.1 ?_
  simpa [IsFixedPt, sub_eq_zero] using hx.2

end TauCeti.SymplecticForm

namespace TauCeti.SymplecticForm

open TopologicalSpace
open scoped Manifold NNReal

/- The fixed-point index is defined for spaces in `Type`. -/
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V)

/-- **Hamiltonian translations count degenerate periodic points by the fixed-point index.** Let
`W` be an open subset of a finite-dimensional symplectic vector space such that every orbit of `φ`
starting in `W` leaves `W` until time `k > 0`, with `φ` differentiable along these orbits. Let
`f : U → V` be `φ^[k]` on an open set `U ⊆ W`, with compact, possibly degenerate, fixed set. There
is an open neighbourhood `U' ⊆ U` of this fixed set such that, for every `ε > 0`, some smooth
Hamiltonian `H` with compact support inside `W` has a time-one map `ψ` moving no point by more
than `ε` and with derivative within `ε` of the identity everywhere, for which the fixed points of
`(φ ∘ ψ)^[k]` in `U'` are nondegenerate, finitely many, and have signed count
`∑ sign det (1 - d((φ ∘ ψ)^[k])_x)` equal to the fixed-point index of `f`. The conclusions hold
for every Lipschitz constant of the Hamiltonian vector field, one of which exists.

The signed count is the same for every small perturbation with nondegenerate periodic points in
`U'` (`TauCeti.exists_pos_forall_sum_sign_det_iterate_comp_eq_fixedPointIndex`); this theorem
shows that Hamiltonian ones exist. -/
theorem exists_hamiltonianFlow_sum_sign_det_eq_fixedPointIndex {φ : V → V} {k : ℕ} (hk : 0 < k)
    {W : Set V} (hW : IsOpen W) (hφ : ∀ y ∈ W, ∀ j < k, DifferentiableAt ℝ φ (φ^[j] y))
    (hret : ∀ y ∈ W, ∀ j, 0 < j → j < k → φ^[j] y ∉ W) {U : Opens V} (hUW : (U : Set V) ⊆ W)
    (f : C(U, V)) (hf : ∀ z, f z = φ^[k] z) (hfix : IsCompact {z | f z = z}) :
    ∃ U' : Opens V, U' ≤ U ∧ (∀ z, f z = z → (z : V) ∈ U') ∧ ∀ {ε : ℝ}, 0 < ε →
      ∃ H : V → ℝ, ContDiff ℝ (⊤ : ℕ∞) H ∧ HasCompactSupport H ∧ tsupport H ⊆ W ∧
        (∃ L, LipschitzWith L (ω.hamiltonianVectorField H)) ∧
        ∀ {L : ℝ≥0} (hX : LipschitzWith L (ω.hamiltonianVectorField H)),
          (∀ w, ‖ω.hamiltonianFlow H hX 1 w - w‖ ≤ ε) ∧
          (∀ w, ‖fderiv ℝ (ω.hamiltonianFlow H hX 1) w - ContinuousLinearMap.id ℝ V‖ ≤ ε) ∧
          (∀ z : U', (φ ∘ ω.hamiltonianFlow H hX 1)^[k] z = z →
            IsNondegenerateFixedPt 𝓘(ℝ, V) (φ ∘ ω.hamiltonianFlow H hX 1)^[k] z) ∧
          ∃ hfin : {z : U' | (φ ∘ ω.hamiltonianFlow H hX 1)^[k] z = z}.Finite,
            ∑ z ∈ hfin.toFinset,
                (SignType.sign (1 - fderiv ℝ (φ ∘ ω.hamiltonianFlow H hX 1)^[k] z).det : ℤ) =
              f.fixedPointIndex := by
  obtain ⟨U', hU'U, hfU', hU'c, hU'cU, δ, hδ, hcount⟩ :=
    exists_pos_forall_sum_sign_det_iterate_comp_eq_fixedPointIndex hk hret hUW f hf hfix
  refine ⟨U', hU'U, hfU', fun {ε} hε ↦ ?_⟩
  -- Make the periodic points in the compact closure of `U'` nondegenerate, moving points by less
  -- than `δ`.
  obtain ⟨H, hH, hHc, hHW, hHX, hψ⟩ := ω.exists_hamiltonianFlow_isNondegenerateFixedPt_iterate hk
    hU'c hW (hU'cU.trans hUW) hφ hret (lt_min hε (half_pos hδ))
  refine ⟨H, hH, hHc, hHW, hHX, fun hX ↦ ?_⟩
  obtain ⟨-, hid, hdisp, hderiv, hnd⟩ := hψ hX
  have hnd' (z : U') (hz : (φ ∘ ω.hamiltonianFlow H hX 1)^[k] z = z) :
      IsNondegenerateFixedPt 𝓘(ℝ, V) (φ ∘ ω.hamiltonianFlow H hX 1)^[k] z :=
    hnd z (subset_closure z.property) hz
  refine ⟨fun w ↦ (hdisp w).trans (min_le_left _ _), fun w ↦ (hderiv w).trans (min_le_left _ _),
    hnd', hcount _
    (ω.contDiff_hamiltonianFlow_apply H 0 hX (hH.of_le (by simp)) 1).continuous.continuousOn
    (fun w _ ↦ (hdisp w).trans_lt ((min_le_right _ _).trans_lt (half_lt_self hδ)))
    (fun w hw ↦ (hid w hw).eq_of_nhds) hnd'⟩

end TauCeti.SymplecticForm
