/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.W1p.InteriorMorrey
public import TauCeti.MeasureTheory.Function.PreciseRepresentative
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.Sobolev.Local.Coordinates
import TauCeti.Analysis.Sobolev.Local.W1p
import TauCeti.Analysis.Sobolev.WeakDeriv.Classical
import TauCeti.Topology.MetricSpace.Holder

/-!
# Morrey's embedding for local Sobolev maps on planar domains

Let `Ω ⊆ ℂ` be open, let `F` be a finite-dimensional real normed space and let `2 < p ≤ ∞`.
This file proves that a map `u ∈ W^{1,p}_loc(Ω, F)`, in the sense of `TauCeti.MemWkpLoc p Ω 1`,
has a representative that is continuous on `Ω` and Hölder continuous with exponent
`α = 1 - 2 / p` on compact subsets of `Ω`, with the local Morrey inequality

`‖u*(x) - u*(y)‖ ≤ C ‖Du‖_{Lᵖ(B(x, 2|x - y|))} |x - y|^α` whenever `closedBall x (2|x - y|) ⊆ Ω`.

The representative is the precise representative `u*` of `u`, the limit of its averages over
shrinking balls; it agrees with `u` almost everywhere on `Ω`. The constant `C` depends only on `p`
and `F`. At the endpoint `p = ∞` the exponent is `1` and `u*` is Lipschitz on compact subsets.
Applied to the weak derivative, this shows that a continuous map in `W^{2,p}_loc` is `C¹`.

A real function in `MemWkpLoc p Ω 1` is represented by an element of `W1p volume W p` on every
open `W` with compact closure in `Ω` (`TauCeti.MemWkpLoc.exists_w1p`). The scalar Morrey
inequality is the interior Morrey inequality `TauCeti.W1p.exists_dist_preciseRepresentative_le`
applied on such a `W`; the vector-valued statement follows coordinatewise in a basis of `F`.

## Main declarations

* `TauCeti.MemWkpLoc.continuousOn_preciseRepresentative`: the precise representative is continuous
  on `Ω`.
* `TauCeti.MemWkpLoc.exists_dist_preciseRepresentative_le`: the local Morrey inequality.
* `TauCeti.MemWkpLoc.exists_norm_preciseRepresentative_le`: the local Morrey sup bound
  `‖u*(x)‖ ≤ r^{-2/p} ‖u‖_{Lᵖ(B(x, r))} + C ‖Du‖_{Lᵖ(B(x, 2 r))} r^α`, obtained by averaging the
  local Morrey inequality over `B(x, r)`.
* `TauCeti.MemWkpLoc.eqOn_preciseRepresentative_sub`: precise representatives of members of
  `MemWkpLoc p Ω 1` subtract on `Ω`.
* `TauCeti.MemWkpLoc.exists_holderOnWith_preciseRepresentative_of_isCompact`: Hölder continuity
  with exponent `1 - 2 / p` on compact subsets of `Ω`.
* `TauCeti.MemWkpLoc.exists_lipschitzOnWith_preciseRepresentative_of_isCompact`: the endpoint
  `p = ∞`.
* `TauCeti.MemWkpLoc.contDiffOn_one_of_continuousOn`: a continuous member of `W^{2,p}_loc` is `C¹`
  on `Ω`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Morrey's embedding for local Sobolev spaces).
* L. C. Evans, *Partial Differential Equations*, §5.6.2, Theorem 4.
-/

public section

noncomputable section

open Metric Set MeasureTheory Module TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal Topology

namespace TauCeti

section Planar

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {Ω : Opens ℂ}
  {u : ℂ → F}

/-- The dimension of `ℂ` over `ℝ`, as an extended real exponent, is `2`. -/
private theorem finrank_real_complex_lt (hp : 2 < p) : (finrank ℝ ℂ : ℝ≥0∞) < p := by
  rwa [Complex.finrank_real_complex, Nat.cast_ofNat]

/-- The real-valued case of `TauCeti.MemWkpLoc.continuousOn_preciseRepresentative`. -/
private theorem continuousOn_preciseRepresentative_real (hp : 2 < p) {u : ℂ → ℝ}
    (hu : MemWkpLoc p Ω 1 u) : ContinuousOn (preciseRepresentative volume u) Ω := by
  have : Fact (1 ≤ p) := ⟨one_le_two.trans hp.le⟩
  obtain ⟨D, hD, -⟩ := hu.exists_weakFDeriv_of_isOpen
  intro x hx
  obtain ⟨W, hxW, hWΩ, hWc⟩ :=
    Opens.exists_between_and_isCompact_closure isCompact_singleton (singleton_subset_iff.2 hx)
  obtain ⟨v, hv, -⟩ := hu.exists_w1p hD hWc hWΩ
  have heq : EqOn (preciseRepresentative volume u) (preciseRepresentative volume (W1p.value v))
      W := fun z hz => (preciseRepresentative_congr_ae_nhds (W.isOpen.mem_nhds hz) hv).symm
  exact (((W1p.continuousOn_preciseRepresentative (finrank_real_complex_lt hp) v).congr
    heq).continuousAt (W.isOpen.mem_nhds (hxW rfl))).continuousWithinAt

/-- The real-valued case of `TauCeti.MemWkpLoc.exists_dist_preciseRepresentative_le`. -/
private theorem exists_dist_preciseRepresentative_le_real (hp : 2 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Opens ℂ} {u : ℂ → ℝ} {D : ℂ → ℂ →L[ℝ] ℝ}, MemWkpLoc p Ω 1 u →
      HasWeakFDerivOn volume Ω u D → ∀ {x y : ℂ}, closedBall x (2 * dist x y) ⊆ Ω →
        dist (preciseRepresentative volume u x) (preciseRepresentative volume u y) ≤
          C * (eLpNorm D p (volume.restrict (ball x (2 * dist x y)))).toReal *
            dist x y ^ (((1 : ℝ≥0∞) - 2 / p).toNNReal : ℝ) := by
  have : Fact (1 ≤ p) := ⟨one_le_two.trans hp.le⟩
  obtain ⟨C, hC, hdist⟩ :=
    W1p.exists_dist_preciseRepresentative_le (mu := (volume : Measure ℂ))
      (finrank_real_complex_lt hp)
  refine ⟨C, hC, fun {Ω u D} hu hD x y hxy => ?_⟩
  obtain ⟨W, hBW, hWΩ, hWc⟩ :=
    Opens.exists_between_and_isCompact_closure (isCompact_closedBall _ _) hxy
  obtain ⟨v, hv, hgrad⟩ := hu.exists_w1p hD hWc hWΩ
  have hW : ∀ z ∈ closedBall x (2 * dist x y),
      preciseRepresentative volume (W1p.value v) z = preciseRepresentative volume u z :=
    fun z hz => preciseRepresentative_congr_ae_nhds (W.isOpen.mem_nhds (hBW hz)) hv
  have hy : y ∈ closedBall x (2 * dist x y) := by
    rw [mem_closedBall, dist_comm]
    linarith [dist_nonneg (x := x) (y := y)]
  have hnorm : eLpNorm (W1p.gradient v : ℂ → ℂ) p (volume.restrict (ball x (2 * dist x y))) =
      eLpNorm D p (volume.restrict (ball x (2 * dist x y))) := by
    have hBW' : volume.restrict (ball x (2 * dist x y)) ≤ volume.restrict (W : Set ℂ) :=
      Measure.restrict_mono (ball_subset_closedBall.trans hBW) le_rfl
    refine eLpNorm_congr_norm_ae ((Lp.aestronglyMeasurable _).mono_measure hBW')
      ((memLpLoc_iff.1 (hu.memLpLoc_of_hasWeakFDerivOn hD) _ hxy
        (isCompact_closedBall _ _)).mono_measure
          (Measure.restrict_mono ball_subset_closedBall le_rfl)).aestronglyMeasurable ?_
    filter_upwards [ae_mono (Measure.restrict_mono (ball_subset_closedBall.trans hBW) le_rfl)
      hgrad] with z hz
    rw [hz, LinearIsometryEquiv.norm_map]
  have h := hdist v hBW
  rwa [hW x (mem_closedBall_self (by positivity)), hW y hy, hnorm, Complex.finrank_real_complex,
    Nat.cast_ofNat] at h

variable [FiniteDimensional ℝ F]

/-- In the basis `Module.finBasis ℝ F`, the precise representative of `u ∈ MemWkpLoc p Ω 1` is,
on `Ω`, the sum of the precise representatives of the coordinates of `u` times the basis vectors.
In particular it is continuous on `Ω`. -/
private theorem eqOn_preciseRepresentative_coord (hp : 2 < p) (hu : MemWkpLoc p Ω 1 u) :
    EqOn (preciseRepresentative volume u)
      (fun z => ∑ i, preciseRepresentative volume
        (fun w => ((Module.finBasis ℝ F).coord i).toContinuousLinearMap (u w)) z •
          Module.finBasis ℝ F i) Ω ∧
    ContinuousOn (fun z => ∑ i, preciseRepresentative volume
        (fun w => ((Module.finBasis ℝ F).coord i).toContinuousLinearMap (u w)) z •
          Module.finBasis ℝ F i) Ω := by
  set b := Module.finBasis ℝ F
  set ℓ : Fin (finrank ℝ F) → F →L[ℝ] ℝ := fun i => (b.coord i).toContinuousLinearMap
  have hp1 : 1 ≤ p := one_le_two.trans hp.le
  have hcont : ContinuousOn
      (fun z => ∑ i, preciseRepresentative volume (fun w => ℓ i (u w)) z • b i) Ω :=
    continuousOn_finsetSum _ fun i _ =>
      (continuousOn_preciseRepresentative_real hp (hu.clm_comp (ℓ i))).smul continuousOn_const
  exact ⟨b.eqOn_preciseRepresentative_sum_repr hp1 hu.memLpLoc fun i =>
    continuousOn_preciseRepresentative_real hp (hu.clm_comp (ℓ i)), hcont⟩

/-- **Continuity of `W^{1,p}_loc` maps for `p > 2`.** The precise representative of
`u ∈ MemWkpLoc p Ω 1`, which agrees with `u` almost everywhere on `Ω`
(`TauCeti.MemLpLoc.ae_eq_preciseRepresentative`), is continuous on `Ω`. -/
theorem MemWkpLoc.continuousOn_preciseRepresentative (hp : 2 < p) (hu : MemWkpLoc p Ω 1 u) :
    ContinuousOn (preciseRepresentative volume u) Ω :=
  let h := eqOn_preciseRepresentative_coord hp hu
  h.2.congr h.1

/-- For `p > 2`, on `Ω` the precise representative of a difference of members of
`MemWkpLoc p Ω 1` is the difference of their precise representatives, both being continuous
there. -/
theorem MemWkpLoc.eqOn_preciseRepresentative_sub (hp : 2 < p) {f g : ℂ → F}
    (hf : MemWkpLoc p Ω 1 f) (hg : MemWkpLoc p Ω 1 g) :
    EqOn (preciseRepresentative volume (f - g))
      (preciseRepresentative volume f - preciseRepresentative volume g) Ω := by
  have hp1 : 1 ≤ p := one_le_two.trans hp.le
  refine eqOn_preciseRepresentative_of_continuousOn Ω.isOpen
    ((hf.sub hg).memLpLoc.locallyIntegrableOn hp1 Ω.isOpen.isLocallyClosed) ?_
    ((hf.continuousOn_preciseRepresentative hp).sub (hg.continuousOn_preciseRepresentative hp))
  filter_upwards [hf.memLpLoc.ae_eq_preciseRepresentative hp1,
    hg.memLpLoc.ae_eq_preciseRepresentative hp1] with z hfz hgz
  simp only [Pi.sub_apply, hfz, hgz]

/-- **The local Morrey inequality for `W^{1,p}_loc` maps.** Let `2 < p ≤ ∞` and `α = 1 - 2 / p`.
There is a constant `C > 0`, depending only on `p` and `F`, such that the following holds. Let
`u ∈ MemWkpLoc p Ω 1` with weak derivative `D` on `Ω`, and let `x, y` be points with
`closedBall x (2 |x - y|) ⊆ Ω`. Then the precise representative `u*` of `u` satisfies

`‖u*(x) - u*(y)‖ ≤ C ‖D‖_{Lᵖ(B(x, 2 |x - y|))} |x - y|^α`. -/
theorem MemWkpLoc.exists_dist_preciseRepresentative_le (hp : 2 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Opens ℂ} {u : ℂ → F} {D : ℂ → ℂ →L[ℝ] F}, MemWkpLoc p Ω 1 u →
      HasWeakFDerivOn volume Ω u D → ∀ {x y : ℂ}, closedBall x (2 * dist x y) ⊆ Ω →
        dist (preciseRepresentative volume u x) (preciseRepresentative volume u y) ≤
          C * (eLpNorm D p (volume.restrict (ball x (2 * dist x y)))).toReal *
            dist x y ^ (((1 : ℝ≥0∞) - 2 / p).toNNReal : ℝ) := by
  obtain ⟨C₀, hC₀, h₀⟩ := exists_dist_preciseRepresentative_le_real hp
  set b := Module.finBasis ℝ F
  set ℓ : Fin (finrank ℝ F) → F →L[ℝ] ℝ := fun i => (b.coord i).toContinuousLinearMap
  refine ⟨C₀ * (1 + ∑ i, ‖ℓ i‖ * ‖b i‖), by positivity, fun {Ω u D} hu hD x y hxy => ?_⟩
  set B := ball x (2 * dist x y)
  set N := (eLpNorm D p (volume.restrict B)).toReal
  set a : ℝ := dist x y ^ (((1 : ℝ≥0∞) - 2 / p).toNNReal : ℝ)
  have hBK : volume.restrict B ≤ volume.restrict (closedBall x (2 * dist x y)) :=
    Measure.restrict_mono ball_subset_closedBall le_rfl
  have hDfin : eLpNorm D p (volume.restrict B) ≠ ∞ :=
    ((memLpLoc_iff.1 (hu.memLpLoc_of_hasWeakFDerivOn hD) _ hxy
      (isCompact_closedBall _ _)).mono_measure hBK).eLpNorm_ne_top
  have hcoord : ∀ i, dist (preciseRepresentative volume (fun w => ℓ i (u w)) x)
      (preciseRepresentative volume (fun w => ℓ i (u w)) y) ≤ C₀ * (‖ℓ i‖ * N) * a := by
    intro i
    refine (h₀ (hu.clm_comp (ℓ i)) (hD.clm_comp (ℓ i)) hxy).trans ?_
    gcongr
    have hmeas : AEStronglyMeasurable (fun z => (ℓ i).comp (D z)) (volume.restrict B) :=
      ((memLpLoc_iff.1 ((hu.clm_comp (ℓ i)).memLpLoc_of_hasWeakFDerivOn (hD.clm_comp (ℓ i))) _ hxy
        (isCompact_closedBall _ _)).mono_measure hBK).aestronglyMeasurable
    have hle := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas
      (ae_of_all _ fun z => (ℓ i).opNorm_comp_le (D z)) p
    refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDfin) hle).trans_eq ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
  have hx : x ∈ (Ω : Set ℂ) := hxy (mem_closedBall_self (by positivity))
  have hy : y ∈ (Ω : Set ℂ) := hxy (by
    rw [mem_closedBall, dist_comm]
    linarith [dist_nonneg (x := x) (y := y)])
  have heq := (eqOn_preciseRepresentative_coord hp hu).1
  rw [heq hx, heq hy, dist_eq_norm, ← Finset.sum_sub_distrib]
  calc ‖∑ i, (preciseRepresentative volume (fun w => ℓ i (u w)) x • b i -
          preciseRepresentative volume (fun w => ℓ i (u w)) y • b i)‖
      ≤ ∑ i, ‖preciseRepresentative volume (fun w => ℓ i (u w)) x • b i -
          preciseRepresentative volume (fun w => ℓ i (u w)) y • b i‖ := norm_sum_le _ _
    _ = ∑ i, dist (preciseRepresentative volume (fun w => ℓ i (u w)) x)
          (preciseRepresentative volume (fun w => ℓ i (u w)) y) * ‖b i‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← sub_smul, norm_smul, Real.norm_eq_abs, Real.dist_eq]
    _ ≤ ∑ i, C₀ * (‖ℓ i‖ * N) * a * ‖b i‖ := by
        gcongr with i
        exact hcoord i
    _ = C₀ * (∑ i, ‖ℓ i‖ * ‖b i‖) * N * a := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ C₀ * (1 + ∑ i, ‖ℓ i‖ * ‖b i‖) * N * a := by
        gcongr
        linarith

/-- **The local Morrey sup bound.** Let `2 < p ≤ ∞` and `α = 1 - 2 / p`. There is a constant
`C > 0`, depending only on `p` and `F`, such that the following holds. Let `u ∈ MemWkpLoc p Ω 1`
with weak derivative `D` on `Ω`, let `r > 0` and let `x` be a point with `closedBall x (2 r) ⊆ Ω`.
Then the precise representative `u*` of `u` satisfies

`‖u*(x)‖ ≤ r^{-2/p} ‖u‖_{Lᵖ(B(x, r))} + C ‖D‖_{Lᵖ(B(x, 2 r))} r^α`.

The proof averages the local Morrey inequality
`TauCeti.MemWkpLoc.exists_dist_preciseRepresentative_le` over `B(x, r)`. -/
theorem MemWkpLoc.exists_norm_preciseRepresentative_le (hp : 2 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Opens ℂ} {u : ℂ → F} {D : ℂ → ℂ →L[ℝ] F}, MemWkpLoc p Ω 1 u →
      HasWeakFDerivOn volume Ω u D → ∀ {x : ℂ} {r : ℝ}, 0 < r → closedBall x (2 * r) ⊆ Ω →
        ‖preciseRepresentative volume u x‖ ≤
          r ^ (-(2 / p.toReal)) * (eLpNorm u p (volume.restrict (ball x r))).toReal +
            C * (eLpNorm D p (volume.restrict (ball x (2 * r)))).toReal *
              r ^ (((1 : ℝ≥0∞) - 2 / p).toNNReal : ℝ) := by
  obtain ⟨C, hC, hdist⟩ := MemWkpLoc.exists_dist_preciseRepresentative_le (F := F) hp
  refine ⟨C, hC, fun {Ω u D} hu hD x r hr hxr => ?_⟩
  have hp1 : 1 ≤ p := one_le_two.trans hp.le
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  set α : ℝ := (((1 : ℝ≥0∞) - 2 / p).toNNReal : ℝ)
  set B := ball x r
  set N := (eLpNorm D p (volume.restrict (ball x (2 * r)))).toReal
  set A := C * N * r ^ α
  set c := preciseRepresentative volume u x
  have hBK : B ⊆ closedBall x (2 * r) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hBΩ : B ⊆ Ω := hBK.trans hxr
  have hDfin : eLpNorm D p (volume.restrict (ball x (2 * r))) ≠ ∞ :=
    ((memLpLoc_iff.1 (hu.memLpLoc_of_hasWeakFDerivOn hD) _ hxr
      (isCompact_closedBall _ _)).mono_measure
        (Measure.restrict_mono ball_subset_closedBall le_rfl)).eLpNorm_ne_top
  -- Pointwise: `‖u*(x)‖ ≤ ‖u*(y)‖ + A` for `y ∈ B`.
  have hpt : ∀ y ∈ B, ‖c‖ ≤ ‖preciseRepresentative volume u y‖ + A := by
    intro y hy
    have hxy : dist x y < r := by
      rw [dist_comm]
      exact hy
    have hsub : closedBall x (2 * dist x y) ⊆ closedBall x (2 * r) :=
      closedBall_subset_closedBall (by linarith)
    have h := hdist hu hD (hsub.trans hxr)
    have h2 : dist c (preciseRepresentative volume u y) ≤ A := by
      refine h.trans ?_
      have hN : (eLpNorm D p (volume.restrict (ball x (2 * dist x y)))).toReal ≤ N :=
        ENNReal.toReal_mono hDfin (eLpNorm_mono_measure _
          (Measure.restrict_mono (ball_subset_ball (by linarith)) le_rfl))
      have hα : dist x y ^ α ≤ r ^ α :=
        Real.rpow_le_rpow dist_nonneg hxy.le NNReal.zero_le_coe
      have := mul_le_mul hN hα (Real.rpow_nonneg dist_nonneg _)
        (ENNReal.toReal_nonneg.trans hN)
      calc _ = C * ((eLpNorm D p (volume.restrict (ball x (2 * dist x y)))).toReal *
            dist x y ^ α) := by ring
        _ ≤ C * (N * r ^ α) := by gcongr
        _ = A := by ring
    calc ‖c‖ ≤ ‖preciseRepresentative volume u y‖ +
          ‖c - preciseRepresentative volume u y‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ _ := by
        rw [← dist_eq_norm]
        linarith
  have hae : ∀ᵐ y ∂volume.restrict B, ‖c‖ ≤ ‖u y‖ + A := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hBΩ
      (hu.memLpLoc.ae_eq_preciseRepresentative hp1), self_mem_ae_restrict measurableSet_ball]
      with y hy hyB
    rw [hy]
    exact hpt y hyB
  have huB : MemLp u p (volume.restrict B) :=
    (memLpLoc_iff.1 hu.memLpLoc _ hxr (isCompact_closedBall _ _)).mono_measure
      (Measure.restrict_mono hBK le_rfl)
  -- Integrate the pointwise bound in `Lᵖ(B)`.
  have hle : eLpNorm (fun _ : ℂ => c) p (volume.restrict B) ≤
      eLpNorm u p (volume.restrict B) + eLpNorm (fun _ : ℂ => A) p (volume.restrict B) := by
    calc _ ≤ eLpNorm (fun y => ‖u y‖ + A) p (volume.restrict B) :=
          eLpNorm_mono_ae_real aestronglyMeasurable_const hae
      _ ≤ eLpNorm (fun y => ‖u y‖) p (volume.restrict B) +
          eLpNorm (fun _ : ℂ => A) p (volume.restrict B) :=
          eLpNorm_add_le hp1
      _ = _ := by rw [eLpNorm_norm _ huB.aestronglyMeasurable]
  have hV : volume B = ENNReal.ofReal r ^ 2 * NNReal.pi := Complex.volume_ball x r
  have hVpos : volume B ≠ 0 := (measure_ball_pos volume x hr).ne'
  have hVfin : volume B ≠ ∞ := measure_ball_lt_top.ne
  have hμ : volume.restrict B ≠ 0 := by
    rwa [Ne, Measure.restrict_eq_zero]
  rw [eLpNorm_const _ hp0 hμ, eLpNorm_const _ hp0 hμ, Measure.restrict_apply_univ] at hle
  set s : ℝ := 1 / p.toReal
  have hs : 0 ≤ s := by positivity
  set V := (volume B).toReal
  have hVr : V = r ^ 2 * Real.pi := by
    simp only [V, hV, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le,
      ENNReal.coe_toReal, NNReal.coe_real_pi]
  have hVs : r ^ (2 * s) ≤ V ^ s := by
    rw [Real.rpow_mul hr.le, hVr]
    refine Real.rpow_le_rpow (by positivity) ?_ hs
    rw [Real.rpow_two]
    nlinarith [Real.two_le_pi, sq_nonneg r]
  have hrs : 0 < r ^ (2 * s) := Real.rpow_pos_of_pos hr _
  have hVs0 : 0 < V ^ s := hrs.trans_le hVs
  have hufin : eLpNorm u p (volume.restrict B) ≠ ∞ := huB.eLpNorm_ne_top
  -- Take real parts: `‖c‖ V^s ≤ ‖u‖_{Lᵖ(B)} + A V^s`.
  have hreal : ‖c‖ * V ^ s ≤ (eLpNorm u p (volume.restrict B)).toReal + A * V ^ s := by
    have hA : 0 ≤ A := by
      have := ENNReal.toReal_nonneg (a := eLpNorm D p (volume.restrict (ball x (2 * r))))
      positivity
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hufin, ENNReal.mul_ne_top
      enorm_ne_top (ENNReal.rpow_ne_top_of_nonneg hs hVfin)⟩) hle
    rwa [ENNReal.toReal_add hufin (ENNReal.mul_ne_top enorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hs hVfin)), ENNReal.toReal_mul, ENNReal.toReal_mul,
      toReal_enorm, toReal_enorm, Real.norm_of_nonneg hA,
      ← ENNReal.toReal_rpow] at h
  have hexp : r ^ (-(2 / p.toReal)) = (r ^ (2 * s))⁻¹ := by
    rw [← Real.rpow_neg hr.le]
    congr 1
    simp only [s]
    ring
  rw [hexp]
  have _hU := ENNReal.toReal_nonneg (a := eLpNorm u p (volume.restrict B))
  have key : ‖c‖ - A ≤ (eLpNorm u p (volume.restrict B)).toReal / V ^ s := by
    rw [le_div_iff₀ hVs0]
    linarith
  calc ‖c‖ ≤ (eLpNorm u p (volume.restrict B)).toReal / V ^ s + A := by linarith
    _ ≤ (eLpNorm u p (volume.restrict B)).toReal / r ^ (2 * s) + A := by
        gcongr
    _ = _ := by
        rw [div_eq_mul_inv, mul_comm]

/-- **Morrey's embedding for `W^{1,p}_loc` maps on compact sets.** If `2 < p ≤ ∞`, the precise
representative of `u ∈ MemWkpLoc p Ω 1` is Hölder continuous with exponent `1 - 2 / p` on every
compact subset of `Ω`. -/
theorem MemWkpLoc.exists_holderOnWith_preciseRepresentative_of_isCompact (hp : 2 < p)
    (hu : MemWkpLoc p Ω 1 u) {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0, HolderOnWith C ((1 : ℝ≥0∞) - 2 / p).toNNReal
      (preciseRepresentative volume u) K := by
  set f := preciseRepresentative volume u
  obtain ⟨C, hC, hdist⟩ := MemWkpLoc.exists_dist_preciseRepresentative_le (F := F) hp
  obtain ⟨D, hD, -⟩ := hu.exists_weakFDeriv_of_isOpen
  obtain ⟨R, hR, hRK⟩ := hK.exists_cthickening_subset_open Ω.isOpen hKΩ
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    ((hu.continuousOn_preciseRepresentative hp).mono hKΩ)
  have hRc : IsCompact (cthickening R K) := hK.cthickening
  have hDfin : eLpNorm D p (volume.restrict (cthickening R K)) ≠ ∞ :=
    (memLpLoc_iff.1 (hu.memLpLoc_of_hasWeakFDerivOn hD) _ hRK hRc).eLpNorm_ne_top
  set N := (eLpNorm D p (volume.restrict (cthickening R K))).toReal
  refine ⟨_, HolderOnWith.of_dist_lt_of_dist_le (K := (C * N).toNNReal) (D := (2 * M).toNNReal)
    (Real.toNNReal_pos.2 (half_pos hR)) (fun x hx y _ hd => ?_) fun x hx y hy => ?_⟩
  · -- Nearby points: the local Morrey inequality on `closedBall x (2 |x - y|) ⊆ Ω`.
    rw [Real.coe_toNNReal _ (half_pos hR).le] at hd
    rw [Real.coe_toNNReal _ (mul_nonneg hC.le ENNReal.toReal_nonneg)]
    have hsub : closedBall x (2 * dist x y) ⊆ cthickening R K :=
      (closedBall_subset_cthickening hx _).trans (cthickening_mono (by linarith) K)
    refine (hdist hu hD (hsub.trans hRK)).trans ?_
    gcongr
    exact ball_subset_closedBall.trans hsub
  · -- Distant points: `‖f x - f y‖ ≤ 2M`.
    calc dist (f x) (f y) ≤ ‖f x‖ + ‖f y‖ := dist_le_norm_add_norm _ _
      _ ≤ 2 * M := by linarith [hM x hx, hM y hy]
      _ ≤ (2 * M).toNNReal := Real.le_coe_toNNReal _

/-- **`W^{1,∞}_loc` maps are locally Lipschitz.** At the endpoint `p = ∞` the Morrey exponent
`1 - 2 / p` is `1`: the precise representative of `u ∈ MemWkpLoc ∞ Ω 1` is Lipschitz on every
compact subset of `Ω`. -/
theorem MemWkpLoc.exists_lipschitzOnWith_preciseRepresentative_of_isCompact
    (hu : MemWkpLoc ∞ Ω 1 u) {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0, LipschitzOnWith C (preciseRepresentative volume u) K := by
  obtain ⟨C, hC⟩ :=
    hu.exists_holderOnWith_preciseRepresentative_of_isCompact ENNReal.ofNat_lt_top hK hKΩ
  simp only [ENNReal.div_top, tsub_zero, ENNReal.toNNReal_one] at hC
  exact ⟨C, holderOnWith_one.1 hC⟩

/-- **Continuous `W^{2,p}_loc` maps are `C¹` for `p > 2`.** The weak derivative of
`u ∈ MemWkpLoc p Ω 2` is in `W^{1,p}_loc`, so it agrees almost everywhere with its continuous
precise representative, which is then a continuous weak derivative of `u`. If `u` itself is
continuous on `Ω`, it is therefore `C¹` there. -/
theorem MemWkpLoc.contDiffOn_one_of_continuousOn (hp : 2 < p) (hv : MemWkpLoc p Ω 2 u)
    (hc : ContinuousOn u Ω) : ContDiffOn ℝ 1 u Ω := by
  have : CompleteSpace F := FiniteDimensional.complete ℝ F
  obtain ⟨D, hD, hD1⟩ := hv.exists_weakFDeriv_of_isOpen
  have hD' := hD.congr_ae_deriv (hD1.memLpLoc.ae_eq_preciseRepresentative (one_le_two.trans hp.le))
  simpa using hD'.contDiffOn_succ hc (n := 0)
    (contDiffOn_zero.2 (hD1.continuousOn_preciseRepresentative hp))

end Planar

end TauCeti
