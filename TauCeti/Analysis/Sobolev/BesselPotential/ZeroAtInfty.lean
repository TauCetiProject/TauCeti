/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
public import TauCeti.Analysis.Sobolev.BesselPotential.Multiplication
public import TauCeti.Analysis.Sobolev.BesselPotential.Operator
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.MeasureTheory.Function.ZeroAtInftyRepresentative
import TauCeti.Analysis.Calculus.ContDiff.OperatorFamily
import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic

/-!
# The bounded Sobolev embeddings of `H^s(ℝⁿ)` into `C₀` and `C^k`

Let `E` be a finite-dimensional real inner product space of dimension `n` and `F` a complex Hilbert
space. An element `u` of the Bessel-potential space `H^s(E, F) = H^{s,2}(E, F)` with `s > n / 2` is
an `L²` function with a unique continuous representative, which vanishes at infinity and is `C^k`
when `s > k + n / 2` (`TemperedDistribution.MemSobolev.exists_zeroAtInftyContinuousMap_ae_eq`,
`TemperedDistribution.MemSobolev.contDiff_of_ae_eq`). This file bundles these embeddings as
bounded operators.

* `BesselPotentialSpace.toZeroAtInfty`: the **Sobolev embedding** `H^s(E, F) →L[ℂ] C₀(E, F)` for
  `s > n / 2`, sending `u` to its continuous representative. Its image is `C^k` for
  `s > k + n / 2`, with derivatives of order at most `k` bounded by a constant times `‖u‖_{H^s}`.
  It turns multiplication by a Schwartz function `φ` into pointwise multiplication
  (`BesselPotentialSpace.toZeroAtInfty_smulLeftCLM_apply`).
* `BesselPotentialSpace.smulLeftContDiffMapSupportedIn`: for a Schwartz function `φ` with
  topological support in a compact set `K` and `s > k + n / 2`, the bounded operator
  `H^s(E, F) →L[ℂ] 𝓓^{k}_{K}(E, F)` sending `u` to the continuous representative of `φ u`. The
  target is Mathlib's space of `C^k` functions vanishing outside `K`, with the topology of uniform
  convergence of all derivatives of order at most `k`.

For a finite-dimensional fibre `F` the second operator is compact
(`BesselPotentialSpace.isCompactOperator_smulLeftContDiffMapSupportedIn`).

Along a `Cⁿ` family `U : P → H^s(E, F)` with `s > n + dim E / 2`, the continuous representatives
are `Cⁿ` jointly in the parameter and the point: `p ↦ u_p (g p)` is `Cⁿ` for every `Cⁿ` map `g`
(`ContDiff.toZeroAtInfty_apply`). This follows from the regularity of evaluation on spaces of
`C^n` functions with derivatives bounded by the norm
(`TauCeti.contDiffOn_apply_of_forall_norm_iteratedFDeriv_le`).

## References

* G. B. Folland, *Introduction to Partial Differential Equations*, 2nd ed., Princeton University
  Press, 1995, Chapter 6 (the Sobolev embedding `H_s ⊆ C^k` for `s > k + n / 2`).
-/

public section

noncomputable section

open MeasureTheory Module Set TemperedDistribution Filter TopologicalSpace
open scoped SchwartzMap BesselPotentialSpace ZeroAtInfty Distributions

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

namespace BesselPotentialSpace

open TauCeti (nonneg_of_finrank_lt_two_mul)

variable {s r : ℝ}

/-! ### The Sobolev embedding into `C₀` -/

/-- An element of `H^s`, `s > dim E / 2`, has a continuous representative vanishing at
infinity. -/
private theorem exists_inclusionLp_ae_eq (h0 : 0 ≤ s) (hs : finrank ℝ E < 2 * s)
    (u : H^{s}(E, F)) : ∃ g : C₀(E, F), inclusionLp h0 u =ᵐ[volume] g :=
  MemSobolev.exists_zeroAtInftyContinuousMap_ae_eq hs (memSobolev_inclusionLp h0 u)

/-- The continuous representative of an element of `H^s`, `s > dim E / 2`, as a linear map. -/
private def toZeroAtInftyₗ (hs : finrank ℝ E < 2 * s) : H^{s}(E, F) →ₗ[ℂ] C₀(E, F) :=
  TauCeti.zeroAtInftyRepresentativeₗ (exists_inclusionLp_ae_eq (nonneg_of_finrank_lt_two_mul hs) hs)
    (fun u v ↦ by simpa only [map_add] using Lp.coeFn_add (inclusionLp _ u) (inclusionLp _ v))
    (fun c u ↦ by simpa only [map_smul] using Lp.coeFn_smul c (inclusionLp _ u))

private theorem coeFn_inclusionLp_ae_eq_toZeroAtInftyₗ (h0 : 0 ≤ s) (hs : finrank ℝ E < 2 * s)
    (u : H^{s}(E, F)) : inclusionLp h0 u =ᵐ[volume] toZeroAtInftyₗ hs u :=
  TauCeti.ae_eq_zeroAtInftyRepresentativeₗ (exists_inclusionLp_ae_eq h0 hs) _ _ u

/-- The derivatives of order at most `k` of a continuous representative of `u ∈ H^s`,
`s > k + dim E / 2`, are bounded by a constant times `‖u‖_{H^s}`. -/
private theorem exists_norm_iteratedFDeriv_le_of_ae_eq (h0 : 0 ≤ s) {k : ℕ}
    (hk : finrank ℝ E < 2 * (s - k)) :
    ∃ C, 0 ≤ C ∧ ∀ (u : H^{s}(E, F)) {g : E → F}, Continuous g →
      inclusionLp h0 u =ᵐ[volume] g → ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    TemperedDistribution.exists_norm_iteratedFDeriv_le_mul_norm_toBesselPotentialSpace (F := F) hk
  refine ⟨C, hC, fun u g hg hug j hj x ↦ ?_⟩
  exact (hbound (memSobolev_inclusionLp h0 u) hg hug j hj x).trans_eq
    (by rw [toBesselPotentialSpace_memSobolev_inclusionLp])

/-- **The Sobolev embedding `H^s(E, F) →L[ℂ] C₀(E, F)`** for `s > dim E / 2`: the bounded linear
map sending an element of the Bessel-potential space `H^s` to its unique representative that is
continuous and vanishes at infinity (`BesselPotentialSpace.toZeroAtInfty_eq_iff`). -/
def toZeroAtInfty (hs : finrank ℝ E < 2 * s) : H^{s}(E, F) →L[ℂ] C₀(E, F) :=
  (toZeroAtInftyₗ hs).mkContinuousOfExistsBound <| by
    have h0 : 0 ≤ s := nonneg_of_finrank_lt_two_mul hs
    obtain ⟨C, hC, hbound⟩ := exists_norm_iteratedFDeriv_le_of_ae_eq (F := F) h0 (k := 0)
      (by simpa using hs)
    refine ⟨C, fun u ↦ ?_⟩
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
      BoundedContinuousFunction.norm_le (by positivity)]
    intro x
    simpa using hbound u (toZeroAtInftyₗ hs u).continuous
      (coeFn_inclusionLp_ae_eq_toZeroAtInftyₗ h0 hs u) 0 le_rfl x

section ZeroAtInfty

variable {hs : finrank ℝ E < 2 * s}

/-- The Sobolev embedding sends `u ∈ H^s` to a representative of the `L²` function `u`. -/
theorem coeFn_inclusionLp_ae_eq_toZeroAtInfty (h0 : 0 ≤ s) (u : H^{s}(E, F)) :
    inclusionLp h0 u =ᵐ[volume] toZeroAtInfty hs u :=
  coeFn_inclusionLp_ae_eq_toZeroAtInftyₗ h0 hs u

/-- The Sobolev embedding of `u ∈ H^s` is the only function in `C₀` representing the `L²`
function `u`. -/
theorem toZeroAtInfty_eq_iff (h0 : 0 ≤ s) (u : H^{s}(E, F)) (g : C₀(E, F)) :
    toZeroAtInfty hs u = g ↔ inclusionLp h0 u =ᵐ[volume] g :=
  TauCeti.zeroAtInftyRepresentativeₗ_eq_iff (exists_inclusionLp_ae_eq h0 hs) _ _ u g

/-- The tempered distribution `u ∈ H^s`, `s > dim E / 2`, is integration against its Sobolev
embedding. -/
theorem toDistr_apply_eq_integral_toZeroAtInfty (u : H^{s}(E, F)) (φ : 𝓢(E, ℂ)) :
    u.toDistr φ = ∫ x, φ x • toZeroAtInfty hs u x := by
  have h0 : 0 ≤ s := nonneg_of_finrank_lt_two_mul hs
  rw [← toTemperedDistribution_inclusionLp h0, Lp.toTemperedDistribution_apply]
  exact integral_congr_ae <|
    (coeFn_inclusionLp_ae_eq_toZeroAtInfty (hs := hs) h0 u).mono fun x hx ↦ by simp only [hx]

/-- The Sobolev embedding depends only on the underlying tempered distribution, not on the order
of the Bessel-potential space it is taken in. -/
theorem toZeroAtInfty_congr {hr : finrank ℝ E < 2 * r} {u : H^{s}(E, F)} {v : H^{r}(E, F)}
    (h : u.toDistr = v.toDistr) : toZeroAtInfty hs u = toZeroAtInfty hr v := by
  have h0 : 0 ≤ s := nonneg_of_finrank_lt_two_mul hs
  have hr0 : 0 ≤ r := nonneg_of_finrank_lt_two_mul hr
  have huv : inclusionLp h0 u = inclusionLp hr0 v := by
    rw [inclusionLp_eq_iff, toTemperedDistribution_inclusionLp, h]
  rw [toZeroAtInfty_eq_iff h0, huv]
  exact coeFn_inclusionLp_ae_eq_toZeroAtInfty hr0 v

/-- The Sobolev embedding commutes with the inclusions `H^s ⊆ H^r`. -/
theorem toZeroAtInfty_inclusion {hr : finrank ℝ E < 2 * r} (h : r ≤ s) (u : H^{s}(E, F)) :
    toZeroAtInfty hr (inclusion h u) = toZeroAtInfty hs u :=
  toZeroAtInfty_congr (toDistr_inclusion h u)

/-- The Sobolev embedding is injective. -/
theorem toZeroAtInfty_injective :
    Function.Injective (toZeroAtInfty hs : H^{s}(E, F) → C₀(E, F)) := by
  have h0 : 0 ≤ s := nonneg_of_finrank_lt_two_mul hs
  intro u v huv
  refine inclusionLp_injective h0 (Lp.ext ?_)
  filter_upwards [coeFn_inclusionLp_ae_eq_toZeroAtInfty (hs := hs) h0 u,
    coeFn_inclusionLp_ae_eq_toZeroAtInfty (hs := hs) h0 v] with x hu hv
  rw [hu, hv, huv]

/-- The Sobolev embedding of the element of `H^s(E)` of a continuous real Sobolev function `f` is
`f` itself. -/
theorem coe_toZeroAtInfty_ofRealSobolevFunction {h0 : 0 ≤ s} {f : E → ℝ}
    {hf : f ∈ realSobolevFunctions E s 2} (hfc : Continuous f) :
    ⇑(toZeroAtInfty hs (ofRealSobolevFunction h0 hf)) = fun x ↦ (f x : ℂ) :=
  (Continuous.ae_eq_iff_eq volume (toZeroAtInfty hs _).continuous
    (Complex.continuous_ofReal.comp hfc)).1 <|
      (coeFn_inclusionLp_ae_eq_toZeroAtInfty h0 _).symm.trans
        (coeFn_inclusionLp_ofRealSobolevFunction h0 hf)

/-- On Schwartz functions the Sobolev embedding is the inclusion `𝓢(E, F) ⊆ C₀(E, F)`. -/
@[simp]
theorem toZeroAtInfty_toBesselPotentialSpaceCLM (f : 𝓢(E, F)) :
    toZeroAtInfty hs (SchwartzMap.toBesselPotentialSpaceCLM s 2 f) = f.toZeroAtInfty := by
  have h0 : 0 ≤ s := nonneg_of_finrank_lt_two_mul hs
  rw [toZeroAtInfty_eq_iff h0, inclusionLp_toBesselPotentialSpaceCLM]
  filter_upwards [f.coeFn_toLp 2 volume] with x hx
  rw [hx, SchwartzMap.toZeroAtInfty_apply]

/-- The Sobolev embedding turns multiplication by a Schwartz function `φ` into pointwise
multiplication by `φ`. -/
@[simp]
theorem toZeroAtInfty_smulLeftCLM_apply (φ : 𝓢(E, ℂ)) (u : H^{s}(E, F)) (x : E) :
    toZeroAtInfty hs (smulLeftCLM s φ u) x = φ x • toZeroAtInfty hs u x := by
  have h0 : 0 ≤ s := nonneg_of_finrank_lt_two_mul hs
  refine congrFun ((Continuous.ae_eq_iff_eq volume (map_continuous (toZeroAtInfty hs _))
    (φ.continuous.smul (map_continuous (toZeroAtInfty hs u)))).1 ?_) x
  filter_upwards [coeFn_inclusionLp_ae_eq_toZeroAtInfty (hs := hs) h0 (smulLeftCLM s φ u),
    coeFn_inclusionLp_ae_eq_smul_of_toDistr_eq_smulLeftCLM h0 h0 φ.hasTemperateGrowth
      (φ.norm_le_seminorm ℂ) (toDistr_smulLeftCLM s φ u),
    coeFn_inclusionLp_ae_eq_toZeroAtInfty (hs := hs) h0 u]
    with y hφu hφ hu
  rw [Pi.smul_apply', ← hφu, hφ, hu]

/-- The Sobolev embedding of `φ u` vanishes outside the topological support of the Schwartz
function `φ`. -/
theorem toZeroAtInfty_smulLeftCLM_eq_zero_of_notMem_tsupport (φ : 𝓢(E, ℂ)) (u : H^{s}(E, F)) {x : E}
    (hx : x ∉ tsupport φ) : toZeroAtInfty hs (smulLeftCLM s φ u) x = 0 := by
  rw [toZeroAtInfty_smulLeftCLM_apply, image_eq_zero_of_notMem_tsupport hx, zero_smul]

end ZeroAtInfty

/-- **Sobolev embedding into `C^k`.** The Sobolev embedding of `u ∈ H^s`, `s > k + dim E / 2`, is
`k` times continuously differentiable. -/
theorem contDiff_toZeroAtInfty {k : ℕ} (hk : finrank ℝ E + 2 * k < 2 * s) (u : H^{s}(E, F)) :
    ContDiff ℝ k (toZeroAtInfty (by linarith) u) := by
  have h0 : 0 ≤ s := nonneg_of_finrank_lt_two_mul (E := E) (by linarith)
  exact MemSobolev.contDiff_of_ae_eq (by linarith) (memSobolev_inclusionLp h0 u)
    (toZeroAtInfty _ u).continuous (coeFn_inclusionLp_ae_eq_toZeroAtInfty h0 u)

/-- **The quantitative Sobolev embedding into `C^k`.** For `s > k + dim E / 2` there is a
constant `C` such that the derivatives of order at most `k` of the Sobolev embedding of every
`u ∈ H^s` are bounded by `C ‖u‖_{H^s}`. -/
theorem exists_norm_iteratedFDeriv_toZeroAtInfty_le {k : ℕ}
    (hk : finrank ℝ E + 2 * k < 2 * s) :
    ∃ C, 0 ≤ C ∧ ∀ (u : H^{s}(E, F)) (j : ℕ), j ≤ k → ∀ x,
      ‖iteratedFDeriv ℝ j (toZeroAtInfty (by linarith) u) x‖ ≤ C * ‖u‖ := by
  have h0 : 0 ≤ s := nonneg_of_finrank_lt_two_mul (E := E) (by linarith)
  obtain ⟨C, hC, hbound⟩ := exists_norm_iteratedFDeriv_le_of_ae_eq (F := F) h0 (k := k)
    (by linarith)
  exact ⟨C, hC, fun u ↦ hbound u (toZeroAtInfty _ u).continuous
    (coeFn_inclusionLp_ae_eq_toZeroAtInfty h0 u)⟩

/-! ### The embedding into `C^k` functions with a fixed compact support -/

variable {k : ℕ} {φ : 𝓢(E, ℂ)} {K : Compacts E}

variable (F) in
/-- The linear map underlying `BesselPotentialSpace.smulLeftContDiffMapSupportedIn`. -/
private def smulLeftContDiffMapSupportedInₗ (hk : finrank ℝ E + 2 * k < 2 * s)
    (hφ : tsupport φ ⊆ K) : H^{s}(E, F) →ₗ[ℂ] 𝓓^{k}_{K}(E, F) where
  toFun u := .of_support_subset (contDiff_toZeroAtInfty hk (smulLeftCLM s φ u)) <|
    Function.support_subset_iff'.2 fun _ hx ↦
      toZeroAtInfty_smulLeftCLM_eq_zero_of_notMem_tsupport φ u fun h ↦ hx (hφ h)
  map_add' u v := ContDiffMapSupportedIn.ext fun x ↦ by
    simp [ContDiffMapSupportedIn.coe_of_support_subset]
  map_smul' c u := ContDiffMapSupportedIn.ext fun x ↦ by
    simp [ContDiffMapSupportedIn.coe_of_support_subset]

variable (F) in
/-- **The Sobolev embedding into `C^k` with a fixed compact support.** For a Schwartz function `φ`
with topological support in a compact set `K` and `s > k + dim E / 2`, the bounded operator
`H^s(E, F) → 𝓓^{k}_{K}(E, F)` sending `u` to the Sobolev embedding of `φ u`, which is `φ` times
the Sobolev embedding of `u` (`BesselPotentialSpace.coe_smulLeftContDiffMapSupportedIn`), a `C^k`
function vanishing outside `K`. -/
def smulLeftContDiffMapSupportedIn (hk : finrank ℝ E + 2 * k < 2 * s) (hφ : tsupport φ ⊆ K) :
    H^{s}(E, F) →L[ℂ] 𝓓^{k}_{K}(E, F) where
  toLinearMap := smulLeftContDiffMapSupportedInₗ F hk hφ
  cont := by
    obtain ⟨C, hC, hbound⟩ := exists_norm_iteratedFDeriv_toZeroAtInfty_le (F := F) hk
    set M := ‖(smulLeftCLM s φ : H^{s}(E, F) →L[ℂ] H^{s}(E, F))‖
    refine WithSeminorms.continuous_of_isBounded (norm_withSeminorms ℂ H^{s}(E, F))
      (ContDiffMapSupportedIn.withSeminorms ℂ E F k K) _
      (.of_real fun i ↦ ⟨{()}, C * M, fun u ↦ ?_⟩)
    have hCu : 0 ≤ C * M * ‖u‖ := by positivity
    refine le_of_le_of_eq ((ContDiffMapSupportedIn.seminorm_le_iff ℂ hCu i
      (smulLeftContDiffMapSupportedInₗ F hk hφ u)).2 fun hi x _ ↦ ?_) (by simp)
    calc ‖iteratedFDeriv ℝ i (toZeroAtInfty _ (smulLeftCLM s φ u)) x‖
        ≤ C * ‖smulLeftCLM s φ u‖ := hbound _ i (by exact_mod_cast hi) x
      _ ≤ C * M * ‖u‖ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left ((smulLeftCLM s φ).le_opNorm u) hC

/-- The embedding sends `u` to `φ` times the Sobolev embedding of `u`. -/
@[simp]
theorem coe_smulLeftContDiffMapSupportedIn (hk : finrank ℝ E + 2 * k < 2 * s)
    (hφ : tsupport φ ⊆ K) (u : H^{s}(E, F)) :
    ⇑(smulLeftContDiffMapSupportedIn F hk hφ u) =
      (φ : E → ℂ) • ⇑(toZeroAtInfty (by linarith) u) := by
  ext x
  simp [smulLeftContDiffMapSupportedIn, smulLeftContDiffMapSupportedInₗ,
    ContDiffMapSupportedIn.coe_of_support_subset]

/-! ### The Sobolev embedding along smooth families -/

/-- **The Sobolev embedding is jointly smooth along smooth families.** Let `s > n + dim E / 2`.
If `U : P → H^s(E, F)` and `g : P → E` are `Cⁿ`, then so is `p ↦ u_p (g p)`, where `u_p` is the
continuous representative of `U p` (`BesselPotentialSpace.toZeroAtInfty`). In particular, for a
`Cⁿ` family `U`, the map `(p, x) ↦ u_p x` is `Cⁿ` jointly in the parameter and the point. -/
theorem _root_.ContDiff.toZeroAtInfty_apply {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {n : ℕ} (hn : finrank ℝ E + 2 * n < 2 * s) {U : P → H^{s}(E, F)} {g : P → E}
    (hU : ContDiff ℝ n U) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n fun p ↦ toZeroAtInfty (by linarith) (U p) (g p) := by
  have hs : finrank ℝ E < 2 * s := by linarith
  -- Evaluation of the embedding at a point, a family of bounded functionals on `H^s` whose
  -- derivatives in the point are bounded by multiples of the `H^s` norm.
  let Φ : E → H^{s}(E, F) →L[ℝ] F := fun y ↦
    (ZeroAtInftyContinuousMap.evalCLM ℝ y).comp ((toZeroAtInfty hs).restrictScalars ℝ)
  have hΦ (u : H^{s}(E, F)) : (fun y ↦ Φ y u) = toZeroAtInfty hs u := by
    ext y
    simp [Φ]
  obtain ⟨C, -, hC⟩ := exists_norm_iteratedFDeriv_toZeroAtInfty_le (F := F) hn
  have h := TauCeti.contDiffOn_apply_of_forall_norm_iteratedFDeriv_le (Φ := Φ) isOpen_univ
    (fun u ↦ by rw [hΦ]; exact (contDiff_toZeroAtInfty hn u).contDiffOn)
    fun m hm _ _ ↦ ⟨C, Filter.Eventually.of_forall fun z u ↦ by rw [hΦ]; exact hC u m hm z⟩
  rw [univ_prod_univ, contDiffOn_univ] at h
  convert h.comp (hU.prodMk hg) using 1
  ext p
  simp [Φ]

end BesselPotentialSpace
