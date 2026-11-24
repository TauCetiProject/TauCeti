/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import TauCeti.Probability.RandomMatrices.GaussianEnsemble.Measure
public import TauCeti.Probability.Independence.Process.HasIndepIncrements
import Mathlib.Probability.Independence.Process.Basic
import TauCeti.Probability.Independence.Pi
import TauCeti.Probability.Independence.Filtration
import TauCeti.Topology.Instances.Matrix

/-!
# Matrix Brownian motion

Real symmetric (`β = 1`) and complex Hermitian (`β = 2`) matrix Brownian motion of size `n`,
started at a matrix `H₀` and driven by a family `B` of real processes indexed by `Fin n × Fin n`:
at time `t` it is `H₀` plus the Gaussian ensemble `TauCeti.Probability.gaussianEnsemble β n` of
the coordinates `B (i, j) t`. When the coordinates are independent standard Brownian motions this
is the matrix Brownian motion of Anderson–Guionnet–Zeitouni, Definition 4.3.1: its entries have
variance `t / n` off the diagonal and `2 t / (β n)` on it, and at time `1` from `H₀ = 0` it is the
GOE or the GUE. It is the matrix process whose ordered eigenvalues Dyson's theorem describes.

Everything here except the laws holds path by path. The laws are stated for coordinates that are
independent pre-Brownian motions, with independence of the coordinates as random paths. The laws
of whole paths also assume each coordinate measurable at every time, so that the path is a
random variable for the product σ-algebra on paths.

Conjugation invariance of the path law reduces questions about the eigenvalues of matrix Brownian
motion from a general symmetric or Hermitian start to a start at the real diagonal matrix of its
eigenvalues, since conjugation does not change eigenvalues.

## Main definitions

* `TauCeti.Probability.matrixBrownian`: matrix Brownian motion started at `H₀`.

## Main results

* `TauCeti.Probability.isHermitian_matrixBrownian`: it is Hermitian when `H₀` is.
* `TauCeti.Probability.continuous_matrixBrownian` and
  `TauCeti.Probability.ae_continuous_matrixBrownian`: continuity of the paths.
* `TauCeti.Probability.matrixBrownian_add`: restarting at a time `t₀` gives matrix Brownian
  motion from the current value, driven by the shifted coordinates.
* `TauCeti.Probability.smul_matrixBrownian_mul` and
  `TauCeti.Probability.identDistrib_matrixBrownian_mul`: Brownian scaling.
* `TauCeti.Probability.hasLaw_matrixBrownian_sub`: an increment over `[s, t]` has the law of
  `√(t - s)` times the GOE or GUE.
* `TauCeti.Probability.indepFun_matrixBrownian_shift`: the increments after `t₀` are independent
  of the path up to `t₀`.
* `TauCeti.Probability.hasIndepIncrements_matrixBrownian`: independent increments.
* `TauCeti.Probability.identDistrib_linearMap_matrixBrownian`: the image of the path under a
  real-linear map preserving the GOE or GUE law is matrix Brownian motion in law, started at the
  image of `H₀`.
* `TauCeti.Probability.identDistrib_mul_matrixBrownian_one_mul_conjTranspose` and
  `TauCeti.Probability.identDistrib_mul_matrixBrownian_two_mul_conjTranspose`: orthogonal
  (`β = 1`) and unitary (`β = 2`) conjugation invariance of the path law.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §4.3.1.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §3.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

namespace TauCeti

namespace Probability

variable {Ω : Type*}

/-- **Matrix Brownian motion** of size `n` started at `H₀`: at time `t` it is `H₀` plus the
Gaussian ensemble of the coordinates `B (i, j) t`, a real symmetric noise for `β = 1` and a
complex Hermitian one otherwise. For independent standard Brownian coordinates and a Hermitian
`H₀` this is real symmetric (`β = 1`) or complex Hermitian (`β = 2`) Brownian motion in the
normalization of Anderson–Guionnet–Zeitouni, Definition 4.3.1. -/
def matrixBrownian (β n : ℕ) (H₀ : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin n × Fin n → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : Matrix (Fin n) (Fin n) ℂ :=
  H₀ + gaussianEnsemble β n (fun ij ↦ B ij t ω)

variable {β n : ℕ} {H₀ : Matrix (Fin n) (Fin n) ℂ} {B : Fin n × Fin n → ℝ≥0 → Ω → ℝ}

/-- Unfolding `matrixBrownian`: the start plus the Gaussian ensemble of the coordinates. -/
theorem matrixBrownian_def (t : ℝ≥0) (ω : Ω) :
    matrixBrownian β n H₀ B t ω = H₀ + gaussianEnsemble β n (fun ij ↦ B ij t ω) := (rfl)

/-- Matrix Brownian motion started at a Hermitian matrix is Hermitian at every time and for
every path. -/
theorem isHermitian_matrixBrownian (hH₀ : H₀.IsHermitian) (t : ℝ≥0) (ω : Ω) :
    (matrixBrownian β n H₀ B t ω).IsHermitian :=
  hH₀.add (isHermitian_gaussianEnsemble β n _)

/-- An increment of matrix Brownian motion is the Gaussian ensemble of the increments of the
coordinates; it does not depend on the start. -/
theorem matrixBrownian_sub_matrixBrownian (s t : ℝ≥0) (ω : Ω) :
    matrixBrownian β n H₀ B t ω - matrixBrownian β n H₀ B s ω =
      gaussianEnsemble β n (fun ij ↦ B ij t ω - B ij s ω) := by
  rw [matrixBrownian_def, matrixBrownian_def, add_sub_add_left_eq_sub, ← gaussianEnsemble_sub,
    Pi.sub_def]

/-- **Restart at a time `t₀`.** Matrix Brownian motion after time `t₀` is matrix Brownian motion
started at its value at `t₀` and driven by the coordinate increments after `t₀`. -/
theorem matrixBrownian_add (t₀ t : ℝ≥0) (ω : Ω) :
    matrixBrownian β n H₀ B (t₀ + t) ω =
      matrixBrownian β n (matrixBrownian β n H₀ B t₀ ω)
        (fun ij t ω ↦ B ij (t₀ + t) ω - B ij t₀ ω) t ω := by
  rw [matrixBrownian_def, matrixBrownian_def, matrixBrownian_def, add_assoc,
    ← gaussianEnsemble_add]
  congr 2
  funext ij
  simp

/-- **Brownian scaling.** For `c ≥ 0`, `(√c)⁻¹` times matrix Brownian motion at time `c t` is
matrix Brownian motion at time `t` started at `(√c)⁻¹ H₀` and driven by the rescaled coordinates
`(√c)⁻¹ B (i, j) (c t)`, which are again Brownian motions when `c ≠ 0`
(`ProbabilityTheory.IsBrownianReal.smul`). -/
theorem smul_matrixBrownian_mul (c t : ℝ≥0) (ω : Ω) :
    (√c)⁻¹ • matrixBrownian β n H₀ B (c * t) ω =
      matrixBrownian β n ((√c)⁻¹ • H₀) (fun ij t ω ↦ (√c)⁻¹ * B ij (c * t) ω) t ω := by
  rw [matrixBrownian_def, matrixBrownian_def, smul_add, ← gaussianEnsemble_smul, Pi.smul_def]
  simp_rw [smul_eq_mul]

/-- If every coordinate starts at `0`, matrix Brownian motion starts at `H₀`. -/
theorem matrixBrownian_zero {ω : Ω} (h : ∀ ij, B ij 0 ω = 0) :
    matrixBrownian β n H₀ B 0 ω = H₀ := by
  simp [matrixBrownian_def, h, ← Pi.zero_def]

/-- If every coordinate path is continuous, so is the path of matrix Brownian motion. -/
theorem continuous_matrixBrownian {ω : Ω} (h : ∀ ij, Continuous (B ij · ω)) :
    Continuous (matrixBrownian β n H₀ B · ω) :=
  continuous_const.add (continuous_gaussianEnsemble.comp (continuous_pi h))

/-- Matrix Brownian motion at a fixed time is measurable when its coordinates are. -/
theorem measurable_matrixBrownian [MeasurableSpace Ω] {t : ℝ≥0}
    (h : ∀ ij, Measurable (B ij t)) : Measurable (matrixBrownian β n H₀ B t) :=
  (continuous_const.add continuous_gaussianEnsemble).measurable.comp (Measurable.of_eval h)

/-- Matrix Brownian motion is jointly measurable in time and randomness when its coordinates
are. -/
theorem measurable_uncurry_matrixBrownian [MeasurableSpace Ω]
    (h : ∀ ij, Measurable (Function.uncurry (B ij))) :
    Measurable (Function.uncurry (matrixBrownian β n H₀ B)) :=
  (continuous_const.add continuous_gaussianEnsemble).measurable.comp (Measurable.of_eval h)

section Law

variable [MeasurableSpace Ω] {P : Measure Ω}

/-- Matrix Brownian motion at a fixed time is almost everywhere measurable when its coordinates
are. -/
theorem aemeasurable_matrixBrownian {t : ℝ≥0} (h : ∀ ij, AEMeasurable (B ij t) P) :
    AEMeasurable (matrixBrownian β n H₀ B t) P :=
  (continuous_const.add continuous_gaussianEnsemble).measurable.comp_aemeasurable
    (AEMeasurable.of_eval h)

/-- Matrix Brownian motion with pre-Brownian coordinates starts at `H₀` almost surely. -/
theorem ae_matrixBrownian_zero (hB : ∀ ij, IsPreBrownianReal (B ij) P) :
    ∀ᵐ ω ∂P, matrixBrownian β n H₀ B 0 ω = H₀ := by
  filter_upwards [ae_all_iff.2 fun ij ↦ (hB ij).eval_zero_ae_eq_zero] with ω hω
  exact matrixBrownian_zero hω

/-- Matrix Brownian motion with Brownian coordinates has almost surely continuous paths. -/
theorem ae_continuous_matrixBrownian (hB : ∀ ij, IsBrownianReal (B ij) P) :
    ∀ᵐ ω ∂P, Continuous (matrixBrownian β n H₀ B · ω) := by
  filter_upwards [ae_all_iff.2 fun ij ↦ (hB ij).cont] with ω hω
  exact continuous_matrixBrownian hω

/-- **The law at a fixed time.** With independent pre-Brownian coordinates, matrix Brownian motion
at time `t` has the law of `H₀` plus `√t` times the GOE (`β = 1`) or GUE (`β = 2`). -/
theorem hasLaw_matrixBrownian (hB : ∀ ij, IsPreBrownianReal (B ij) P)
    (hindep : iIndepFun (fun ij ω t ↦ B ij t ω) P) (t : ℝ≥0) :
    HasLaw (matrixBrownian β n H₀ B t)
      ((Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map
        fun x ↦ H₀ + √t • gaussianEnsemble β n x) P := by
  have h := hasLaw_gaussianEnsemble β (fun ij ↦ (hB ij).hasLaw_eval t)
    (hindep.comp (fun _ f ↦ f t) fun _ ↦ measurable_pi_apply t)
  have hcomp : (fun x ↦ H₀ + √t • gaussianEnsemble β n x) =
      (H₀ + ·) ∘ fun x ↦ √t • gaussianEnsemble β n x := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop)]
  exact (⟨by fun_prop, rfl⟩ : HasLaw (H₀ + ·) _ _).comp h

/-- **The law of an increment.** With independent pre-Brownian coordinates, for `s ≤ t` the
increment of matrix Brownian motion over `[s, t]` has the law `gaussianEnsembleLaw β n` of the
GOE (`β = 1`) or GUE (`β ≠ 1`), scaled by `√(t - s)`. -/
theorem hasLaw_matrixBrownian_sub (hB : ∀ ij, IsPreBrownianReal (B ij) P)
    (hindep : iIndepFun (fun ij ω t ↦ B ij t ω) P) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ matrixBrownian β n H₀ B t ω - matrixBrownian β n H₀ B s ω)
      ((gaussianEnsembleLaw β n).map (√(t - s : ℝ≥0) • ·)) P := by
  have hdist : nndist (t : ℝ) s = t - s := by
    refine NNReal.eq ?_
    rw [coe_nndist, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hst)),
      NNReal.coe_sub hst]
  rw [gaussianEnsembleLaw_def, Measure.map_map (by fun_prop) measurable_gaussianEnsemble,
    Function.comp_def]
  simp_rw [matrixBrownian_sub_matrixBrownian]
  exact hasLaw_gaussianEnsemble β (fun ij ↦ hdist ▸ (hB ij).hasLaw_sub t s)
    (hindep.comp (fun _ f ↦ f t - f s) fun _ ↦ by fun_prop)

/-- **Brownian scaling in law.** With independent pre-Brownian coordinates, matrix Brownian motion
from `0` at time `c t` has the law of `√c` times matrix Brownian motion from `0` at time `t`. -/
theorem identDistrib_matrixBrownian_mul (hB : ∀ ij, IsPreBrownianReal (B ij) P)
    (hindep : iIndepFun (fun ij ω t ↦ B ij t ω) P) (c t : ℝ≥0) :
    IdentDistrib (matrixBrownian β n 0 B (c * t))
      (fun ω ↦ √c • matrixBrownian β n 0 B t ω) P P := by
  have hct := hasLaw_matrixBrownian (β := β) (H₀ := 0) hB hindep (c * t)
  have ht := (⟨by fun_prop, rfl⟩ : HasLaw (√c • ·) _ _).comp
    (hasLaw_matrixBrownian (β := β) (H₀ := 0) hB hindep t)
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at ht
  refine ⟨hct.aemeasurable, ht.aemeasurable, ?_⟩
  rw [hct.map_eq, ← Function.comp_def (√c • ·), ht.map_eq]
  congr 1
  funext x
  simp [smul_smul]

/-- **Independent increments.** With independent pre-Brownian coordinates, the increments of
matrix Brownian motion after a time `t₀` are independent of its path up to `t₀`. -/
theorem indepFun_matrixBrownian_shift (hB : ∀ ij, IsPreBrownianReal (B ij) P)
    (hindep : iIndepFun (fun ij ω t ↦ B ij t ω) P) (t₀ : ℝ≥0) :
    IndepFun (fun ω t ↦ matrixBrownian β n H₀ B (t₀ + t) ω - matrixBrownian β n H₀ B t₀ ω)
      (fun ω (t : Set.Iic t₀) ↦ matrixBrownian β n H₀ B t ω) P := by
  have := hindep.isProbabilityMeasure
  refine IndepFun.process_indepFun_process₀ (fun t ↦ ?_)
    (fun t ↦ aemeasurable_matrixBrownian fun ij ↦ (hB ij).aemeasurable _) fun I J ↦ ?_
  · simp_rw [matrixBrownian_sub_matrixBrownian]
    exact measurable_gaussianEnsemble.comp_aemeasurable (AEMeasurable.of_eval fun ij ↦
      ((hB ij).aemeasurable _).sub ((hB ij).aemeasurable _))
  -- the coordinate increments at the times of `I` and the coordinate values at the times of `J`
  let F (ij : Fin n × Fin n) (ω : Ω) (t : I) : ℝ := B ij (t₀ + t) ω - B ij t₀ ω
  let G (ij : Fin n × Fin n) (ω : Ω) (t : J) : ℝ := B ij t ω
  have hF ij : AEMeasurable (F ij) P := AEMeasurable.of_eval fun t ↦
    ((hB ij).aemeasurable _).sub ((hB ij).aemeasurable _)
  have hG ij : AEMeasurable (G ij) P := AEMeasurable.of_eval fun t ↦ (hB ij).aemeasurable _
  have hFG : IndepFun (fun ω ij ↦ F ij ω) (fun ω ij ↦ G ij ω) P :=
    iIndepFun.indepFun_pi_of_indepFun hF hG
      (hindep.comp (fun _ f ↦ ((fun t : I ↦ f (t₀ + t) - f t₀), fun t : J ↦ f t))
        fun _ ↦ by fun_prop)
      fun ij ↦ ((hB ij).indepFun_shift t₀).comp (φ := fun (f : ℝ≥0 → ℝ) (t : I) ↦ f t)
        (ψ := fun (f : Set.Iic t₀ → ℝ) (t : J) ↦ f t) (by fun_prop) (by fun_prop)
  have h := hFG.comp (φ := fun x (t : I) ↦ gaussianEnsemble β n fun ij ↦ x ij t)
    (ψ := fun x (t : J) ↦ H₀ + gaussianEnsemble β n fun ij ↦ x ij t) (by fun_prop)
    (by fun_prop)
  convert h using 1 <;> funext ω t
  · exact matrixBrownian_sub_matrixBrownian _ _ ω
  · exact matrixBrownian_def _ ω

/-- **Independent increments.** With independent pre-Brownian coordinates, each measurable at
every time, matrix Brownian motion has independent increments: its increments over consecutive
time intervals are mutually independent. -/
theorem hasIndepIncrements_matrixBrownian (hB : ∀ ij, IsPreBrownianReal (B ij) P)
    (hBm : ∀ ij t, Measurable (B ij t)) (hindep : iIndepFun (fun ij ω t ↦ B ij t ω) P) :
    HasIndepIncrements (matrixBrownian β n H₀ B) P := by
  have := hindep.isProbabilityMeasure
  have hm (t : ℝ≥0) : StronglyMeasurable (matrixBrownian β n H₀ B t) :=
    (measurable_matrixBrownian (hBm · t)).stronglyMeasurable
  refine Adapted.hasIndepIncrements (ℱ := Filtration.natural _ hm)
    (fun t ↦ (Filtration.stronglyAdapted_natural hm t).measurable) fun s t hst ↦ ?_
  -- the increment over `[s, t]` is the value at `t - s` of the increment process after `s`
  have h := (indepFun_matrixBrownian_shift (β := β) (H₀ := H₀) hB hindep s).comp
    (measurable_pi_apply (t - s)) measurable_id
  simp only [Function.comp_def, id, add_tsub_cancel_of_le hst] at h
  rw [Filtration.natural_eq_comap]
  exact (IndepFun_iff_Indep _ _ _).1 h

/-- **Invariance in law under a linear symmetry of the ensemble.** Let `L` be a real-linear map
of complex matrices that preserves the law `gaussianEnsembleLaw β n` of the GOE (`β = 1`) or
GUE (`β ≠ 1`). With independent pre-Brownian coordinates, each measurable at every time, the
image under `L` of matrix Brownian motion started at `H₀` has, as a process, the law of matrix
Brownian motion started at `L H₀`. -/
theorem identDistrib_linearMap_matrixBrownian (hB : ∀ ij, IsPreBrownianReal (B ij) P)
    (hBm : ∀ ij t, Measurable (B ij t)) (hindep : iIndepFun (fun ij ω t ↦ B ij t ω) P)
    (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (hL : (gaussianEnsembleLaw β n).map L = gaussianEnsembleLaw β n) :
    IdentDistrib (fun ω t ↦ L (matrixBrownian β n H₀ B t ω))
      (fun ω t ↦ matrixBrownian β n (L H₀) B t ω) P P := by
  have := hindep.isProbabilityMeasure
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  have hm (t : ℝ≥0) : Measurable (matrixBrownian β n 0 B t) :=
    measurable_matrixBrownian (hBm · t)
  have hY := hasIndepIncrements_matrixBrownian (β := β) (H₀ := 0) hB hBm hindep
  -- each increment is `√(t - s)` times the ensemble, whose law `L` preserves
  have hlaw (s t : ℝ≥0) (hst : s ≤ t) : IdentDistrib
      (fun ω ↦ L (matrixBrownian β n 0 B t ω) - L (matrixBrownian β n 0 B s ω))
      (fun ω ↦ matrixBrownian β n 0 B t ω - matrixBrownian β n 0 B s ω) P P := by
    have hinc := hasLaw_matrixBrownian_sub (β := β) (H₀ := 0) hB hindep hst
    have hLinc : HasLaw L ((gaussianEnsembleLaw β n).map (√(t - s : ℝ≥0) • ·))
        ((gaussianEnsembleLaw β n).map (√(t - s : ℝ≥0) • ·)) := by
      refine ⟨hLm.aemeasurable, ?_⟩
      rw [Measure.map_map hLm (by fun_prop),
        show ⇑L ∘ (√(t - s : ℝ≥0) • ·) = (√(t - s : ℝ≥0) • ·) ∘ ⇑L from
          funext fun A ↦ map_smul L _ A,
        ← Measure.map_map (by fun_prop) hLm, hL]
    have h := hLinc.comp hinc
    simp only [Function.comp_def, map_sub] at h
    exact ⟨h.aemeasurable, hinc.aemeasurable, h.map_eq.trans hinc.map_eq.symm⟩
  have h0 := ae_matrixBrownian_zero (β := β) (H₀ := 0) hB
  have h := (hY.map' hLm).identDistrib hY (fun t ↦ hLm.comp (hm t)) hm
    (by filter_upwards [h0] with ω hω using by simp [bot_eq_zero', hω])
    (by filter_upwards [h0] with ω hω using by simp [bot_eq_zero', hω]) hlaw
  -- add the start `L H₀` to both paths
  have hshift : Measurable fun (f : ℝ≥0 → Matrix (Fin n) (Fin n) ℂ) t ↦ L H₀ + f t := by
    fun_prop
  convert h.comp hshift using 1 <;> funext ω t <;> simp [matrixBrownian_def]

/-- **Orthogonal invariance in law** (`β = 1`). For a fixed orthogonal matrix `U`, the conjugate
`U H(·) Uᵀ` of real symmetric matrix Brownian motion `H` started at `H₀` has, as a process, the
law of real symmetric matrix Brownian motion started at `U H₀ Uᵀ`. -/
theorem identDistrib_mul_matrixBrownian_one_mul_conjTranspose
    (hB : ∀ ij, IsPreBrownianReal (B ij) P) (hBm : ∀ ij t, Measurable (B ij t))
    (hindep : iIndepFun (fun ij ω t ↦ B ij t ω) P) (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    IdentDistrib
      (fun ω t ↦ (U : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal *
        matrixBrownian 1 n H₀ B t ω * ((U : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal)ᴴ)
      (fun ω t ↦ matrixBrownian 1 n ((U : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal * H₀ *
        ((U : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal)ᴴ) B t ω) P P := by
  have h := identDistrib_linearMap_matrixBrownian (H₀ := H₀) hB hBm hindep
    (LinearMap.mulLeftRight ℝ (((U : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal),
      ((U : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal)ᴴ))
    (by convert map_mul_mul_conjTranspose_gaussianEnsembleLaw_one U using 2
        exact funext fun _ ↦ LinearMap.mulLeftRight_apply _ _ _)
  simpa only [LinearMap.mulLeftRight_apply] using h

/-- **Unitary invariance in law** (`β = 2`). For a fixed unitary matrix `U`, the conjugate
`U H(·) Uᴴ` of complex Hermitian matrix Brownian motion `H` started at `H₀` has, as a process,
the law of complex Hermitian matrix Brownian motion started at `U H₀ Uᴴ`. -/
theorem identDistrib_mul_matrixBrownian_two_mul_conjTranspose
    (hB : ∀ ij, IsPreBrownianReal (B ij) P) (hBm : ∀ ij t, Measurable (B ij t))
    (hindep : iIndepFun (fun ij ω t ↦ B ij t ω) P) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    IdentDistrib
      (fun ω t ↦ (U : Matrix (Fin n) (Fin n) ℂ) * matrixBrownian 2 n H₀ B t ω *
        (U : Matrix (Fin n) (Fin n) ℂ)ᴴ)
      (fun ω t ↦ matrixBrownian 2 n ((U : Matrix (Fin n) (Fin n) ℂ) * H₀ *
        (U : Matrix (Fin n) (Fin n) ℂ)ᴴ) B t ω) P P := by
  have h := identDistrib_linearMap_matrixBrownian (H₀ := H₀) hB hBm hindep
    (LinearMap.mulLeftRight ℝ ((U : Matrix (Fin n) (Fin n) ℂ), (U : Matrix (Fin n) (Fin n) ℂ)ᴴ))
    (by convert map_mul_mul_conjTranspose_gaussianEnsembleLaw_two U using 2
        exact funext fun _ ↦ LinearMap.mulLeftRight_apply _ _ _)
  simpa only [LinearMap.mulLeftRight_apply] using h

end Law

end Probability

end TauCeti
