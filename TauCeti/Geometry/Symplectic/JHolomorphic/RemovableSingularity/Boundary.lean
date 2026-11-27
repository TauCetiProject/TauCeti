/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.RemovableSingularity
public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
import TauCeti.Analysis.Calculus.TangentCone.Basic
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Bootstrap.Boundary
import TauCeti.Analysis.Complex.ReImTopology
import TauCeti.Analysis.InnerProductSpace.Reflection
import TauCeti.Analysis.Sobolev.WeakDeriv.Removable
import TauCeti.MeasureTheory.Integral.NormRpow
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Removal of a finite-energy boundary puncture

Let `x₀` be a point of the real axis and let `u` be a `C³` solution of `∂ₜu = J(u) ∂ₛu` on the
punctured closed half-disc `{0 ≤ im z} ∩ B_R(x₀) \ {x₀}`, with derivatives taken within the
closed upper half-plane `H = {0 ≤ im z}`, mapping the real axis into a subspace `L` of `V` on which
the symplectic form `ω` vanishes. Suppose that `u` has image in a compact set `K`, near which `J`
is `C^ℓ`, `2 ≤ ℓ ≤ ∞`, with `J² = -1` on `K`; that `ω` uniformly tames `J` along `u`; that `J(p)`
exchanges `L` and its orthogonal complement `Lᗮ` for `p ∈ L`; and that `u` has finite energy.
Then `u` has a limit `q ∈ K ∩ L` at the puncture, and the filling `Function.update u x₀ q` is of
class `C^ℓ` on the half-disc `{0 ≤ im z} ∩ B_R(x₀)`, up to the real axis and at the puncture
included, and solves the Cauchy–Riemann equation at every point of it
(`TauCeti.SymplecticForm.exists_contDiffOn_update_inter_of_finite_energy`). This is the boundary
case of the removal of singularities theorem of McDuff–Salamon, Section 4.5, in the flat model
of a constant symplectic form and a linear Lagrangian boundary condition; it is the boundary
counterpart of `TauCeti.SymplecticForm.exists_contDiffOn_update_of_finite_energy`, and the step
which extends the strip and disc bubbles of Gromov compactness across their boundary punctures.

The two conditions on `J(p)` say that `L` is maximal totally real for `J(p)` and orthogonal to
`J(p) L`. The first, `J(p) L ⊆ Lᗮ`, is the hypothesis of the boundary mean-value inequality behind
the continuous filling `TauCeti.SymplecticForm.exists_continuousOn_update_inter_of_finite_energy`.
Together with the second, `J(p) Lᗮ ⊆ L`, it says that `J(p)` anticommutes with the reflection
in `L` (`Submodule.reflection_mul_eq_neg_mul_of_maps_orthogonal`), the form of a totally real
boundary condition taken by elliptic regularity up to the boundary.

The proof has three steps.

* **Higher integrability.** The pointwise bound `‖du(z)‖ ≤ C |z - x₀| ^ (β - 1)`, `β > 0`, of
  `TauCeti.SymplecticForm.exists_pos_norm_fderivWithin_le_rpow` puts `du` in `Lᵖ` on a smaller
  half-disc for some `p > 2`
  (`TauCeti.SymplecticForm.exists_pos_two_lt_memLp_fderivWithin_inter_of_finite_energy`).
* **Weak solution.** The filling is continuous, its derivative within `H` is continuous off the
  puncture, and the puncture lies on the boundary of the open half-disc, where the weak derivative
  is taken. So the filling is a weak solution of `∂ₛu + J(u) ∂ₜu = 0` on the whole half-disc, in
  the sense of `TauCeti.IsWeakCauchyRiemannOn`, with weak derivative locally in `Lᵖ` up to the
  boundary (`TauCeti.SymplecticForm.exists_isWeakCauchyRiemannOn_update_inter_of_finite_energy`).
* **Regularity.** Elliptic bootstrapping at a totally real boundary followed by Morrey's
  embedding up to the axis (`TauCeti.contDiffOn_of_isWeakCauchyRiemannOn_halfPlane`), with the
  reflection in `L` as the involution, makes the filling `C^ℓ` up to the boundary. The classical
  equation at the puncture follows by continuity of both sides, since the punctured half-disc is
  dense in the half-disc (`TauCeti.subset_closure_inter_setOf_im_nonneg_diff_singleton`).

## Main results

In the namespace `TauCeti.SymplecticForm`:

* `exists_pos_two_lt_memLp_fderivWithin_inter_of_finite_energy`: the derivative within the
  half-plane is in `Lᵖ`, for some `p > 2`, on a half-disc about the puncture.
* `exists_isWeakCauchyRiemannOn_update_inter_of_finite_energy`: the filling is a weak solution of
  the Cauchy–Riemann equation on the half-disc, with an exponent `p > 2`.
* `exists_contDiffOn_update_inter_of_finite_energy`: the filling is a `C^ℓ` solution of the
  Cauchy–Riemann equation on the half-disc, up to the boundary and at the puncture.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.5 (removal of singularities, including boundary punctures with totally real boundary
  conditions) and Appendix B.4 (elliptic bootstrapping up to a totally real boundary).
-/

public section

open Complex Filter MeasureTheory Metric Set Topology TopologicalSpace
open scoped RealInnerProductSpace

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {u : ℂ → V} {J : V → V →L[ℝ] V} {R c : ℝ} {W K : Set V} {L : Submodule ℝ V} {x₀ : ℂ}

/-- **Higher integrability at a boundary puncture.** Under the hypotheses of
`TauCeti.SymplecticForm.exists_continuousOn_update_inter_of_finite_energy`, the derivative within
the closed upper half-plane of a finite-energy pseudoholomorphic half-disc belongs to `Lᵖ`, for
some `p > 2`, on a smaller half-disc about the puncture. The puncture is a null set, so no value of
the derivative there is involved. -/
theorem exists_pos_two_lt_memLp_fderivWithin_inter_of_finite_energy
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v)
    (hJL : ∀ p ∈ (L : Set V) ∩ W, ∀ v ∈ L, ∀ w ∈ L, ⟪v, J p w⟫ = 0)
    (hLω : ∀ v ∈ L, ∀ w ∈ L, ω v w = 0) (hx₀ : x₀.im = 0)
    (hu : ContDiffOn ℝ 3 u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})))
    (hCR : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}),
      fderivWithin ℝ u {z | 0 ≤ z.im} z I = J (u z) (fderivWithin ℝ u {z | 0 ≤ z.im} z 1))
    (huL : ∀ z ∈ ball x₀ R \ {x₀}, z.im = 0 → u z ∈ L)
    (huK : MapsTo u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})) K)
    (htame : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}), ∀ v : V,
      c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2)
      ({z | 0 ≤ z.im} ∩ ball x₀ R)) :
    ∃ ε > 0, ε < R ∧ ∃ p : ℝ, 2 < p ∧
      MemLp (fderivWithin ℝ u {z | 0 ≤ z.im}) (ENNReal.ofReal p)
        (volume.restrict ({z | 0 ≤ z.im} ∩ ball x₀ ε)) := by
  set H : Set ℂ := {z | 0 ≤ z.im}
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hJ.continuousOn.mono hKW)
  set M := max B 0
  have hbound : ∀ z ∈ H ∩ (ball x₀ R \ {x₀}), ‖J (u z)‖ ≤ M := fun z hz ↦
    (hB _ (huK hz)).trans (le_max_left _ _)
  obtain ⟨ε, hε, hεR, C, hC, hpoint⟩ := ω.exists_pos_norm_fderivWithin_le_rpow hg hc hR hW hJ hK
    hKW hJsq hJL hLω hx₀ hu hCR huL huK htame hbound henergy
  set β := c / (1 + M) ^ 2
  have hβ : 0 < β := by positivity
  set p := 2 + β
  have hp : 0 < p := by positivity
  refine ⟨ε, hε, hεR, p, by linarith, ?_⟩
  -- The derivative within `H` is continuous off the puncture, which is a null set.
  have hSo : IsOpen (ball x₀ ε \ {x₀}) := isOpen_ball.sdiff isClosed_singleton
  have hSm : MeasurableSet (H ∩ (ball x₀ ε \ {x₀})) :=
    (isClosed_le continuous_const continuous_im).measurableSet.inter
      (measurableSet_ball.diff (measurableSet_singleton _))
  have hcont : ContinuousOn (fderivWithin ℝ u H) (H ∩ (ball x₀ ε \ {x₀})) := by
    have hsmall : ContDiffOn ℝ 3 u (H ∩ (ball x₀ ε \ {x₀})) :=
      hu.mono (inter_subset_inter_right _ (sdiff_subset_sdiff_left (ball_subset_ball hεR.le)))
    refine (hsmall.continuousOn_fderivWithin ((uniqueDiffOn_setOfPred_le_im 0).inter hSo)
      (by norm_num)).congr fun z hz ↦ ?_
    exact (fderivWithin_inter (hSo.mem_nhds hz.2)).symm
  have hnull : volume.restrict (H ∩ (ball x₀ ε \ {x₀})) = volume.restrict (H ∩ ball x₀ ε) := by
    refine Measure.restrict_congr_set ?_
    rw [← inter_sdiff_assoc]
    exact sdiff_null_ae_eq_self (measure_singleton x₀)
  have hmeas : AEStronglyMeasurable (fderivWithin ℝ u H) (volume.restrict (H ∩ ball x₀ ε)) := by
    rw [← hnull]
    exact hcont.aestronglyMeasurable hSm
  rw [← integrable_norm_rpow_iff hmeas (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le]
  -- The majorant `C ^ p ‖z - x₀‖ ^ ((β - 1) p)` is integrable since `(β - 1) p > -2`.
  have hexponent : -(Module.finrank ℝ ℂ : ℝ) < (β - 1) * p := by
    rw [Complex.finrank_real_complex, Nat.cast_ofNat]
    nlinarith [mul_pos hβ hβ]
  have hmajorant : IntegrableOn (fun z ↦ C ^ p * ‖x₀ - z‖ ^ ((β - 1) * p)) (H ∩ ball x₀ ε) :=
    IntegrableOn.mono_set ((integrableOn_norm_sub_rpow_ball (mu := volume) hexponent x₀
      (R := ε)).const_mul (C ^ p)) inter_subset_right
  refine hmajorant.mono' (hmeas.norm.aemeasurable.pow_const p).aestronglyMeasurable ?_
  rw [← hnull]
  filter_upwards [ae_restrict_mem hSm] with z hz
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  calc
    ‖fderivWithin ℝ u H z‖ ^ p ≤ (C * ‖z - x₀‖ ^ (β - 1)) ^ p :=
      Real.rpow_le_rpow (norm_nonneg _) (hpoint z hz) hp.le
    _ = C ^ p * ‖x₀ - z‖ ^ ((β - 1) * p) := by
      rw [Real.mul_rpow hC.le (Real.rpow_nonneg (norm_nonneg _) _),
        ← Real.rpow_mul (norm_nonneg _), norm_sub_rev z x₀]

open Classical in
/-- **The filled boundary puncture is a weak solution.** Under the hypotheses of
`TauCeti.SymplecticForm.exists_continuousOn_update_inter_of_finite_energy`, let `q ∈ K ∩ L` be the
limit of `u` at the puncture. The filling `Function.update u x₀ q` solves the Cauchy–Riemann
equation `∂ₛu + J(u) ∂ₜu = 0` weakly on the whole half-disc `{0 ≤ im z} ∩ B_R(x₀)`, with weak
derivative locally in `Lᵖ` up to the boundary for some `p > 2`. -/
theorem exists_isWeakCauchyRiemannOn_update_inter_of_finite_energy
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v)
    (hJL : ∀ p ∈ (L : Set V) ∩ W, ∀ v ∈ L, ∀ w ∈ L, ⟪v, J p w⟫ = 0)
    (hLω : ∀ v ∈ L, ∀ w ∈ L, ω v w = 0) (hx₀ : x₀.im = 0)
    (hu : ContDiffOn ℝ 3 u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})))
    (hCR : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}),
      fderivWithin ℝ u {z | 0 ≤ z.im} z I = J (u z) (fderivWithin ℝ u {z | 0 ≤ z.im} z 1))
    (huL : ∀ z ∈ ball x₀ R \ {x₀}, z.im = 0 → u z ∈ L)
    (huK : MapsTo u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})) K)
    (htame : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}), ∀ v : V,
      c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2)
      ({z | 0 ≤ z.im} ∩ ball x₀ R)) :
    ∃ q ∈ K ∩ (L : Set V), Tendsto u (𝓝[{z | 0 ≤ z.im} \ {x₀}] x₀) (𝓝 q) ∧
      MapsTo (Function.update u x₀ q) ({z : ℂ | 0 ≤ z.im} ∩ ball x₀ R) K ∧
      ∃ p : ℝ, 2 < p ∧ IsWeakCauchyRiemannOn (ENNReal.ofReal p)
        ({z : ℂ | 0 ≤ z.im} ∩ ball x₀ R) (fun _ ↦ J) 0 (Function.update u x₀ q) := by
  set H : Set ℂ := {z | 0 ≤ z.im}
  obtain ⟨q, hq, hlim, hcont, hmaps⟩ := ω.exists_continuousOn_update_inter_of_finite_energy hg hc
    hR hW hJ hK hKW hJsq hJL hLω hx₀ hu hCR huL huK htame henergy
  obtain ⟨ε, hε, -, p, hp, hmem⟩ := ω.exists_pos_two_lt_memLp_fderivWithin_inter_of_finite_energy
    hg hc hR hW hJ hK hKW hJsq hJL hLω hx₀ hu hCR huL huK htame henergy
  -- The open half-disc `{0 < im z} ∩ B_R(x₀)` misses the puncture, which lies on the axis.
  have hsub : interior (H ∩ ball x₀ R) ⊆ H ∩ (ball x₀ R \ {x₀}) := by
    rw [inter_comm H, interior_inter_setOf_im_nonneg isOpen_ball]
    rintro z ⟨hzb, hzi : 0 < z.im⟩
    refine ⟨by exact hzi.le, hzb, fun hzx ↦ ?_⟩
    rw [mem_singleton_iff.1 hzx, hx₀] at hzi
    exact lt_irrefl _ hzi
  -- The derivative within `H` is continuous off the puncture.
  have hSo : IsOpen (ball x₀ R \ {x₀}) := isOpen_ball.sdiff isClosed_singleton
  have hdcont : ContinuousOn (fderivWithin ℝ u H) (H ∩ (ball x₀ R \ {x₀})) :=
    (hu.continuousOn_fderivWithin ((uniqueDiffOn_setOfPred_le_im 0).inter hSo)
      (by norm_num)).congr fun z hz ↦ (fderivWithin_inter (hSo.mem_nhds hz.2)).symm
  refine ⟨q, hq, hlim, hmaps, p, hp, isWeakCauchyRiemannOn_iff.2
    ⟨hcont, hcont.memLpLoc, fderivWithin ℝ u H, ?_, ?_, ?_⟩⟩
  · -- On the open half-disc the filling is `u`, differentiable with derivative its derivative
    -- within `H`.
    refine hasWeakFDerivOn_of_hasFDerivAt_off_countable (s := ∅) countable_empty
      (hcont.mono interior_subset)
      ((hdcont.mono hsub).locallyIntegrableOn isOpen_interior.measurableSet) fun z hz ↦ ?_
    have hzi : z ∈ interior (H ∩ ball x₀ R) := hz.1
    have hz' : z ∈ H ∩ (ball x₀ R \ {x₀}) := hsub hzi
    have hnhds : H ∩ (ball x₀ R \ {x₀}) ∈ 𝓝 z :=
      mem_of_superset (isOpen_interior.mem_nhds hzi) hsub
    have hdu := ((hu.differentiableOn (by norm_num)) z hz').differentiableAt hnhds
    rw [fderivWithin_of_mem_nhds (mem_of_superset hnhds inter_subset_left)]
    refine hdu.hasFDerivAt.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hz'.2.2] with w hw
    exact Function.update_of_ne hw _ _
  · -- Near the puncture by higher integrability, elsewhere by continuity up to the axis.
    refine memLpLoc_iff_locally.2 fun z hz ↦ ?_
    by_cases hzx : z = x₀
    · subst hzx
      exact ⟨H ∩ ball z ε, mem_nhdsWithin.2 ⟨ball z ε, isOpen_ball, mem_ball_self hε,
        fun w hw ↦ ⟨hw.2.1, hw.1⟩⟩,
        memLpLoc_iff.2 fun T hT _ ↦ hmem.mono_measure (Measure.restrict_mono hT le_rfl)⟩
    · refine ⟨(H ∩ ball x₀ R) ∩ {x₀}ᶜ,
        inter_mem_nhdsWithin _ (isOpen_compl_singleton.mem_nhds hzx), ?_⟩
      refine ContinuousOn.memLpLoc (hdcont.mono ?_)
      exact fun w hw ↦ ⟨hw.1.1, hw.1.2, hw.2⟩
  · -- `∂ₜu = J(u) ∂ₛu` and `J(u)² = -1` give `∂ₛu + J(u) ∂ₜu = 0`.
    refine ae_restrict_of_forall_mem isOpen_interior.measurableSet fun z hz ↦ ?_
    have hz' := hsub hz
    rw [Function.update_of_ne hz'.2.2, hCR z hz', hJsq _ (huK hz')]
    simp

open Classical in
/-- **Removal of a finite-energy boundary puncture** (McDuff–Salamon, Section 4.5). Let `x₀` lie on
the real axis, let `J` be `C^ℓ`, `2 ≤ ℓ ≤ ∞`, near a compact set `K` on which `J² = -1`, and let
`u` be a `C³` solution of `∂ₜu = J(u) ∂ₛu` on the punctured closed half-disc
`{0 ≤ im z} ∩ B_R(x₀) \ {x₀}`, with derivatives taken within the closed upper half-plane, mapping
the real axis into a subspace `L` and the half-disc into `K`. Suppose that `ω` vanishes on `L` and
uniformly tames `J` along `u`, that `J(p)` maps `L` into `Lᗮ` and `Lᗮ` into `L` for `p ∈ L` near
`K`, and that `u` has finite energy. The fixed structure `J₀` identifies the given inner product
with a symplectic metric. Then `u` has a limit `q ∈ K ∩ L` at `x₀` within the half-plane, and the
filling `Function.update u x₀ q` is of class `C^ℓ` on the half-disc `{0 ≤ im z} ∩ B_R(x₀)`, with
image in `K`, and solves the Cauchy–Riemann equation at every point of it, the puncture
included. -/
theorem exists_contDiffOn_update_inter_of_finite_energy {ℓ : ℕ∞} (hℓ : 2 ≤ ℓ)
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ ℓ J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v)
    (hJL : ∀ p ∈ (L : Set V) ∩ W, ∀ v ∈ L, ∀ w ∈ L, ⟪v, J p w⟫ = 0)
    (hJLperp : ∀ p ∈ (L : Set V) ∩ W, ∀ v ∈ Lᗮ, ∀ w ∈ Lᗮ, ⟪v, J p w⟫ = 0)
    (hLω : ∀ v ∈ L, ∀ w ∈ L, ω v w = 0) (hx₀ : x₀.im = 0)
    (hu : ContDiffOn ℝ 3 u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})))
    (hCR : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}),
      fderivWithin ℝ u {z | 0 ≤ z.im} z I = J (u z) (fderivWithin ℝ u {z | 0 ≤ z.im} z 1))
    (huL : ∀ z ∈ ball x₀ R \ {x₀}, z.im = 0 → u z ∈ L)
    (huK : MapsTo u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})) K)
    (htame : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}), ∀ v : V,
      c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2)
      ({z | 0 ≤ z.im} ∩ ball x₀ R)) :
    ∃ q ∈ K ∩ (L : Set V), Tendsto u (𝓝[{z | 0 ≤ z.im} \ {x₀}] x₀) (𝓝 q) ∧
      MapsTo (Function.update u x₀ q) ({z : ℂ | 0 ≤ z.im} ∩ ball x₀ R) K ∧
      ContDiffOn ℝ ℓ (Function.update u x₀ q) ({z : ℂ | 0 ≤ z.im} ∩ ball x₀ R) ∧
      ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ ball x₀ R,
        fderivWithin ℝ (Function.update u x₀ q) {z | 0 ≤ z.im} z I =
          J (Function.update u x₀ q z)
            (fderivWithin ℝ (Function.update u x₀ q) {z | 0 ≤ z.im} z 1) := by
  set H : Set ℂ := {z | 0 ≤ z.im}
  have h2 : (2 : WithTop ℕ∞) ≤ ℓ := WithTop.coe_le_coe.2 hℓ
  obtain ⟨q, hq, hlim, hmaps, p, hp, hweak⟩ :=
    ω.exists_isWeakCauchyRiemannOn_update_inter_of_finite_energy hg hc hR hW (hJ.of_le h2) hK hKW
      hJsq hJL hLω hx₀ hu hCR huL huK htame henergy
  set v := Function.update u x₀ q with hvdef
  -- The boundary values of the filling lie in `L ∩ K`, where `J` anticommutes with the reflection
  -- in `L`.
  have hvL : ∀ s : ℝ, (s : ℂ) ∈ ball x₀ R → v s ∈ L := fun s hs ↦ by
    rcases eq_or_ne (s : ℂ) x₀ with hsx | hsx
    · simpa [hvdef, hsx] using hq.2
    · simpa [hvdef, hsx] using huL s ⟨hs, hsx⟩ (by simp)
  have hJR : ∀ s : ℝ, (s : ℂ) ∈ ball x₀ R → ∀ w,
      L.reflection (J (v s) w) = -J (v s) (L.reflection w) := fun s hs w ↦ by
    have hpLW : v s ∈ (L : Set V) ∩ W := ⟨hvL s hs, hKW (hmaps ⟨by simp, hs⟩)⟩
    simpa using congrArg (fun T : V →L[ℝ] V ↦ T w) (L.reflection_mul_eq_neg_mul_of_maps_orthogonal
      (J (v s)) (fun x hx ↦ (L.mem_orthogonal _).2 fun y hy ↦ hJL _ hpLW y hy x hx)
      (fun x hx ↦ L.orthogonal_orthogonal ▸ (Lᗮ.mem_orthogonal _).2 fun y hy ↦
        hJLperp _ hpLW y hy x hx))
  -- Bootstrap on the half-disc, read as `Ω ∩ {0 ≤ im z}` for the open disc `Ω`.
  let Ω : Opens ℂ := ⟨ball x₀ R, isOpen_ball⟩
  have hΩ : (Ω : Set ℂ) ∩ H = H ∩ ball x₀ R := inter_comm _ _
  have hv : ContDiffOn ℝ ℓ v (H ∩ ball x₀ R) := hΩ ▸
    contDiffOn_of_isWeakCauchyRiemannOn_halfPlane (Ω := Ω) (W := univ ×ˢ W) (J := fun _ ↦ J)
      (η := 0) (R := L.reflection)
      (by simpa using (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hp)
      (isOpen_univ.prod hW) (hJ.comp contDiffOn_snd fun x hx ↦ (mem_prod.1 hx.1).2)
      (by simpa using contDiffOn_const) (fun z hz ↦ ⟨mem_univ _, hKW (hmaps ⟨hz.2, hz.1⟩)⟩)
      (ae_restrict_of_forall_mem (isOpen_ball.measurableSet.inter (isClosed_le continuous_const
        continuous_im).measurableSet) fun z hz ↦
          ContinuousLinearMap.ext (hJsq _ (hmaps ⟨hz.2, hz.1⟩)))
      L.reflection_involutive (fun s hs ↦ L.reflection_mem_subspace_eq_self (hvL s hs)) hJR
      (hΩ ▸ hweak)
  -- Off the puncture the equation is that of `u`; at the puncture it follows by continuity of both
  -- sides. The derivative within `H` is that within the half-disc, which is continuous.
  have hdv : ContinuousOn (fderivWithin ℝ v H) (H ∩ ball x₀ R) :=
    (hv.continuousOn_fderivWithin ((uniqueDiffOn_setOfPred_le_im 0).inter isOpen_ball)
      (le_trans (by norm_num) h2)).congr fun z hz ↦
        (fderivWithin_inter (isOpen_ball.mem_nhds hz.2)).symm
  refine ⟨q, hq, hlim, hmaps, hv, EqOn.of_subset_closure (f := fun z ↦ fderivWithin ℝ v H z I)
    (g := fun z ↦ J (v z) (fderivWithin ℝ v H z 1)) (s := (H ∩ ball x₀ R) \ {x₀}) (fun z hz ↦ ?_)
    (hdv.clm_apply continuousOn_const) (((hJ.continuousOn.mono hKW).comp hv.continuousOn
      hmaps).clm_apply (hdv.clm_apply continuousOn_const)) sdiff_subset ?_⟩
  · have hvu : fderivWithin ℝ v H z = fderivWithin ℝ u H z := by
      refine Filter.EventuallyEq.fderivWithin_eq ?_ (Function.update_of_ne hz.2 _ _)
      filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hz.2)] with w hw
      exact Function.update_of_ne hw _ _
    simp only [hvu]
    rw [hvdef, Function.update_of_ne hz.2]
    exact hCR z ⟨hz.1.1, hz.1.2, hz.2⟩
  · simpa only [inter_comm H] using
      subset_closure_inter_setOf_im_nonneg_diff_singleton isOpen_ball x₀

end TauCeti.SymplecticForm
