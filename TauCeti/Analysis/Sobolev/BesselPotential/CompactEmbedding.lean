/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
public import TauCeti.Analysis.Sobolev.BesselPotential.Rellich
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# Compact Sobolev embeddings of `H^s(ℝⁿ)` into `C^k` with a fixed compact support

Let `E` be a finite-dimensional real inner product space of dimension `n` and `F` a complex Hilbert
space. An element `u` of the Bessel-potential space `H^s(E, F) = H^{s,2}(E, F)` with `s > n / 2` is
an `L²` function with a unique continuous representative, which vanishes at infinity and is `C^k`
when `s > k + n / 2` (`TemperedDistribution.MemSobolev.exists_zeroAtInftyContinuousMap_ae_eq`,
`TemperedDistribution.MemSobolev.contDiff_of_ae_eq`). This file bundles these embeddings as
bounded operators and proves that, for a fixed compact support, the embedding into `C^k` is
compact.

* `BesselPotentialSpace.toZeroAtInfty`: the **Sobolev embedding** `H^s(E, F) →L[ℂ] C₀(E, F)` for
  `s > n / 2`, sending `u` to its continuous representative. Its image is `C^k` for
  `s > k + n / 2`, with derivatives of order at most `k` bounded by a constant times `‖u‖_{H^s}`.
* `BesselPotentialSpace.smulLeftContDiffMapSupportedIn`: for a Schwartz function `φ` with
  topological support in a compact set `K` and `s > k + n / 2`, the bounded operator
  `H^s(E, F) →L[ℂ] 𝓓^{k}_{K}(E, F)` sending `u` to the continuous representative of `φ u`. The
  target is Mathlib's space of `C^k` functions vanishing outside `K`, with the topology of uniform
  convergence of all derivatives of order at most `k`.
* `BesselPotentialSpace.isCompactOperator_smulLeftContDiffMapSupportedIn`: for a
  finite-dimensional fibre `F`, this operator is **compact**. So a bounded set of elements of
  `H^s` supported in a fixed compact set, on a neighbourhood of which `φ = 1`, has relatively
  compact image in `C^k`: every bounded sequence has a subsequence whose derivatives of order at
  most `k` converge uniformly.

The compactness is Rellich's theorem composed with the continuous embedding. Choose an order `r`
with `k + n / 2 < r < s` and a compactly supported Schwartz function `ψ` equal to `1` near the
support of `φ`. Then `φ u = φ (ψ u)`, so the operator factors as `u ↦ ψ u`, which is compact from
`H^s` to `H^r` (`BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM`), followed by
the bounded operator `v ↦ φ v` from `H^r` to `𝓓^{k}_{K}(E, F)`.

## References

* G. B. Folland, *Introduction to Partial Differential Equations*, 2nd ed., Princeton University
  Press, 1995, Chapter 6 (the Sobolev embedding `H_s ⊆ C^k` for `s > k + n / 2` and Rellich's
  theorem for a common compact support).
-/

public section

noncomputable section

open MeasureTheory Module Set TemperedDistribution Filter TopologicalSpace
open scoped SchwartzMap BesselPotentialSpace ZeroAtInfty Distributions

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

namespace BesselPotentialSpace

variable {s r : ℝ}

/-! ### The Sobolev embedding into `C₀` -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- An order above half the dimension is nonnegative. -/
private theorem nonneg_of_finrank_lt (hs : finrank ℝ E < 2 * s) : 0 ≤ s := by
  linarith [(finrank ℝ E).cast_nonneg (α := ℝ)]

/-- An element of `H^s`, `s > dim E / 2`, has a continuous representative vanishing at
infinity. -/
private theorem exists_inclusionLp_ae_eq (h0 : 0 ≤ s) (hs : finrank ℝ E < 2 * s)
    (u : H^{s}(E, F)) : ∃ g : C₀(E, F), inclusionLp h0 u =ᵐ[volume] g := by
  refine MemSobolev.exists_zeroAtInftyContinuousMap_ae_eq hs ?_
  simpa using memSobolev_toLp_inclusion h0 u

/-- Two continuous representatives of the same element of `H^s` coincide. -/
private theorem eq_of_inclusionLp_ae_eq (h0 : 0 ≤ s) {u : H^{s}(E, F)} {g g' : C₀(E, F)}
    (hg : inclusionLp h0 u =ᵐ[volume] g) (hg' : inclusionLp h0 u =ᵐ[volume] g') : g = g' :=
  ZeroAtInftyContinuousMap.ext <| congrFun <|
    (Continuous.ae_eq_iff_eq volume g.continuous g'.continuous).mp (hg.symm.trans hg')

/-- The continuous representative of an element of `H^s`, `s > dim E / 2`, as a linear map. -/
private def toZeroAtInftyₗ (hs : finrank ℝ E < 2 * s) : H^{s}(E, F) →ₗ[ℂ] C₀(E, F) :=
  have h0 : 0 ≤ s := nonneg_of_finrank_lt hs
  { toFun u := (exists_inclusionLp_ae_eq h0 hs u).choose
    map_add' u v := by
      refine eq_of_inclusionLp_ae_eq h0 (u := u + v)
        (exists_inclusionLp_ae_eq h0 hs (u + v)).choose_spec ?_
      filter_upwards [(exists_inclusionLp_ae_eq h0 hs u).choose_spec,
        (exists_inclusionLp_ae_eq h0 hs v).choose_spec,
        Lp.coeFn_add (inclusionLp h0 u) (inclusionLp h0 v)] with x hu hv hadd
      rw [map_add, hadd, Pi.add_apply, hu, hv, _root_.add_apply]
    map_smul' c u := by
      refine eq_of_inclusionLp_ae_eq h0 (u := c • u)
        (exists_inclusionLp_ae_eq h0 hs (c • u)).choose_spec ?_
      filter_upwards [(exists_inclusionLp_ae_eq h0 hs u).choose_spec,
        Lp.coeFn_smul c (inclusionLp h0 u)] with x hu hsmul
      rw [map_smul, hsmul, Pi.smul_apply, hu, RingHom.id_apply, _root_.smul_apply] }

private theorem inclusionLp_ae_eq_toZeroAtInftyₗ (h0 : 0 ≤ s) (hs : finrank ℝ E < 2 * s)
    (u : H^{s}(E, F)) : inclusionLp h0 u =ᵐ[volume] toZeroAtInftyₗ hs u :=
  (exists_inclusionLp_ae_eq _ hs u).choose_spec

/-- The derivatives of order at most `k` of a continuous representative of `u ∈ H^s`,
`s > k + dim E / 2`, are bounded by a constant times `‖u‖_{H^s}`. -/
private theorem exists_norm_iteratedFDeriv_le_of_ae_eq (h0 : 0 ≤ s) {k : ℕ}
    (hk : finrank ℝ E < 2 * (s - k)) :
    ∃ C, 0 ≤ C ∧ ∀ (u : H^{s}(E, F)) {g : E → F}, Continuous g →
      inclusionLp h0 u =ᵐ[volume] g → ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    TemperedDistribution.exists_norm_iteratedFDeriv_le_mul_norm_toBesselPotentialSpace (F := F) hk
  refine ⟨C, hC, fun u g hg hug j hj x ↦ ?_⟩
  have hu : MemSobolev s 2 (inclusionLp h0 u : 𝓢'(E, F)) := by
    simpa using memSobolev_toLp_inclusion h0 u
  have hnorm : hu.toBesselPotentialSpace = u := ext (by simp)
  exact (hbound hu hg hug j hj x).trans_eq (by rw [hnorm])

/-- **The Sobolev embedding `H^s(E, F) →L[ℂ] C₀(E, F)`** for `s > dim E / 2`: the bounded linear
map sending an element of the Bessel-potential space `H^s` to its unique representative that is
continuous and vanishes at infinity (`BesselPotentialSpace.toZeroAtInfty_eq_iff`). -/
def toZeroAtInfty (hs : finrank ℝ E < 2 * s) : H^{s}(E, F) →L[ℂ] C₀(E, F) :=
  (toZeroAtInftyₗ hs).mkContinuousOfExistsBound <| by
    have h0 : 0 ≤ s := nonneg_of_finrank_lt hs
    obtain ⟨C, hC, hbound⟩ := exists_norm_iteratedFDeriv_le_of_ae_eq (F := F) h0 (k := 0)
      (by simpa using hs)
    refine ⟨C, fun u ↦ ?_⟩
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
      BoundedContinuousFunction.norm_le (by positivity)]
    intro x
    simpa using hbound u (toZeroAtInftyₗ hs u).continuous
      (inclusionLp_ae_eq_toZeroAtInftyₗ h0 hs u) 0 le_rfl x

section ZeroAtInfty

variable {hs : finrank ℝ E < 2 * s}

/-- The Sobolev embedding sends `u ∈ H^s` to a representative of the `L²` function `u`. -/
theorem inclusionLp_ae_eq_toZeroAtInfty (h0 : 0 ≤ s) (u : H^{s}(E, F)) :
    inclusionLp h0 u =ᵐ[volume] toZeroAtInfty hs u :=
  inclusionLp_ae_eq_toZeroAtInftyₗ h0 hs u

/-- The Sobolev embedding of `u ∈ H^s` is the only function in `C₀` representing the `L²`
function `u`. -/
theorem toZeroAtInfty_eq_iff (h0 : 0 ≤ s) (u : H^{s}(E, F)) (g : C₀(E, F)) :
    toZeroAtInfty hs u = g ↔ inclusionLp h0 u =ᵐ[volume] g :=
  ⟨fun h ↦ h ▸ inclusionLp_ae_eq_toZeroAtInfty h0 u,
    fun h ↦ eq_of_inclusionLp_ae_eq h0 (inclusionLp_ae_eq_toZeroAtInfty h0 u) h⟩

/-- The tempered distribution `u ∈ H^s`, `s > dim E / 2`, is integration against its Sobolev
embedding. -/
theorem toDistr_apply_eq_integral_toZeroAtInfty (u : H^{s}(E, F)) (φ : 𝓢(E, ℂ)) :
    u.toDistr φ = ∫ x, φ x • toZeroAtInfty hs u x := by
  have h0 : 0 ≤ s := nonneg_of_finrank_lt hs
  rw [← toTemperedDistribution_inclusionLp h0, Lp.toTemperedDistribution_apply]
  exact integral_congr_ae <|
    (inclusionLp_ae_eq_toZeroAtInfty (hs := hs) h0 u).mono fun x hx ↦ by simp only [hx]

/-- The Sobolev embedding depends only on the underlying tempered distribution, not on the order
of the Bessel-potential space it is taken in. -/
theorem toZeroAtInfty_congr {hr : finrank ℝ E < 2 * r} {u : H^{s}(E, F)} {v : H^{r}(E, F)}
    (h : u.toDistr = v.toDistr) : toZeroAtInfty hs u = toZeroAtInfty hr v := by
  have h0 : 0 ≤ s := nonneg_of_finrank_lt hs
  have hr0 : 0 ≤ r := nonneg_of_finrank_lt hr
  have huv : inclusionLp h0 u = inclusionLp hr0 v := by
    rw [inclusionLp_eq_iff, toTemperedDistribution_inclusionLp, h]
  rw [toZeroAtInfty_eq_iff h0, huv]
  exact inclusionLp_ae_eq_toZeroAtInfty hr0 v

/-- The Sobolev embedding commutes with the inclusions `H^s ⊆ H^r`. -/
theorem toZeroAtInfty_inclusion {hr : finrank ℝ E < 2 * r} (h : r ≤ s) (u : H^{s}(E, F)) :
    toZeroAtInfty hr (inclusion h u) = toZeroAtInfty hs u :=
  toZeroAtInfty_congr (toDistr_inclusion h u)

/-- The Sobolev embedding is injective. -/
theorem toZeroAtInfty_injective :
    Function.Injective (toZeroAtInfty hs : H^{s}(E, F) → C₀(E, F)) := by
  have h0 : 0 ≤ s := nonneg_of_finrank_lt hs
  intro u v huv
  refine inclusionLp_injective h0 (Lp.ext ?_)
  filter_upwards [inclusionLp_ae_eq_toZeroAtInfty (hs := hs) h0 u,
    inclusionLp_ae_eq_toZeroAtInfty (hs := hs) h0 v] with x hu hv
  rw [hu, hv, huv]

/-- On Schwartz functions the Sobolev embedding is the inclusion `𝓢(E, F) ⊆ C₀(E, F)`. -/
@[simp]
theorem toZeroAtInfty_toBesselPotentialSpaceCLM (f : 𝓢(E, F)) :
    toZeroAtInfty hs (SchwartzMap.toBesselPotentialSpaceCLM s 2 f) = f.toZeroAtInfty := by
  have h0 : 0 ≤ s := nonneg_of_finrank_lt hs
  rw [toZeroAtInfty_eq_iff h0, inclusionLp_toBesselPotentialSpaceCLM]
  filter_upwards [f.coeFn_toLp 2 volume] with x hx
  rw [hx, SchwartzMap.toZeroAtInfty_apply]

/-- **Sobolev embedding into `C^k`.** The Sobolev embedding of `u ∈ H^s`, `s > k + dim E / 2`, is
`k` times continuously differentiable. -/
theorem contDiff_toZeroAtInfty {k : ℕ} (hk : finrank ℝ E + 2 * k < 2 * s) (u : H^{s}(E, F)) :
    ContDiff ℝ k (toZeroAtInfty hs u) := by
  have h0 : 0 ≤ s := nonneg_of_finrank_lt hs
  refine MemSobolev.contDiff_of_ae_eq (by linarith) ?_ (toZeroAtInfty hs u).continuous
    (inclusionLp_ae_eq_toZeroAtInfty h0 u)
  simpa using memSobolev_toLp_inclusion h0 u

/-- **The quantitative Sobolev embedding into `C^k`.** For `s > k + dim E / 2` there is a
constant `C` such that the derivatives of order at most `k` of the Sobolev embedding of every
`u ∈ H^s` are bounded by `C ‖u‖_{H^s}`. -/
theorem exists_norm_iteratedFDeriv_toZeroAtInfty_le {k : ℕ}
    (hk : finrank ℝ E + 2 * k < 2 * s) :
    ∃ C, 0 ≤ C ∧ ∀ (u : H^{s}(E, F)) (j : ℕ), j ≤ k → ∀ x,
      ‖iteratedFDeriv ℝ j (toZeroAtInfty hs u) x‖ ≤ C * ‖u‖ := by
  have h0 : 0 ≤ s := nonneg_of_finrank_lt hs
  obtain ⟨C, hC, hbound⟩ := exists_norm_iteratedFDeriv_le_of_ae_eq (F := F) h0 (k := k)
    (by linarith)
  exact ⟨C, hC, fun u ↦ hbound u (toZeroAtInfty hs u).continuous
    (inclusionLp_ae_eq_toZeroAtInfty h0 u)⟩

/-- The Sobolev embedding of `φ u` vanishes outside the topological support of the Schwartz
function `φ`. -/
theorem toZeroAtInfty_smulLeftCLM_eq_zero_of_notMem_tsupport (φ : 𝓢(E, ℂ)) (u : H^{s}(E, F)) {x : E}
    (hx : x ∉ tsupport φ) : toZeroAtInfty hs (smulLeftCLM s φ u) x = 0 := by
  have h0 : 0 ≤ s := nonneg_of_finrank_lt hs
  set w := inclusionLp h0 u
  -- The `L²` function of `φ u` is `φ` times the `L²` function of `u`.
  have hloc : LocallyIntegrable (fun y ↦ φ y • w y) volume :=
    locallyIntegrable_iff.2 fun K hK ↦
      (((Lp.memLp w).locallyIntegrable one_le_two).integrableOn_isCompact hK).continuousOn_smul
        φ.continuous.continuousOn hK
  have hφu : inclusionLp h0 (smulLeftCLM s φ u) =ᵐ[volume] fun y ↦ φ y • w y := by
    refine Lp.ae_eq_of_toTemperedDistribution_apply_eq _ hloc fun ψ ↦ ?_
    rw [toTemperedDistribution_inclusionLp, toDistr_smulLeftCLM,
      ← toTemperedDistribution_inclusionLp h0 u,
      Lp.smulLeftCLM_toTemperedDistribution_apply φ.hasTemperateGrowth]
  -- So the continuous representative vanishes almost everywhere, hence everywhere, off
  -- `tsupport φ`.
  have hzero : toZeroAtInfty hs (smulLeftCLM s φ u) =ᵐ[volume.restrict (tsupport φ)ᶜ] 0 := by
    refine EventuallyEq.trans (ae_restrict_of_ae
      ((inclusionLp_ae_eq_toZeroAtInfty (hs := hs) h0 _).symm.trans hφu)) ?_
    filter_upwards [ae_restrict_mem (isClosed_tsupport _).isOpen_compl.measurableSet] with y hy
    simp [image_eq_zero_of_notMem_tsupport hy]
  exact (Measure.eqOn_open_of_ae_eq hzero (isClosed_tsupport _).isOpen_compl
    (toZeroAtInfty hs (smulLeftCLM s φ u)).continuous.continuousOn continuousOn_const) hx

end ZeroAtInfty

/-! ### The embedding into `C^k` functions with a fixed compact support -/

variable {k : ℕ} {φ : 𝓢(E, ℂ)} {K : Compacts E}

variable (F) in
/-- The linear map underlying `BesselPotentialSpace.smulLeftContDiffMapSupportedIn`. -/
private def smulLeftContDiffMapSupportedInₗ (hk : finrank ℝ E + 2 * k < 2 * s)
    (hφ : tsupport φ ⊆ K) : H^{s}(E, F) →ₗ[ℂ] 𝓓^{k}_{K}(E, F) :=
  have hs : finrank ℝ E < 2 * s := by linarith
  { toFun u := .of_support_subset (contDiff_toZeroAtInfty (hs := hs) hk (smulLeftCLM s φ u)) <|
      Function.support_subset_iff'.2 fun _ hx ↦
        toZeroAtInfty_smulLeftCLM_eq_zero_of_notMem_tsupport φ u fun h ↦ hx (hφ h)
    map_add' u v := ContDiffMapSupportedIn.ext fun x ↦ by
      simp [ContDiffMapSupportedIn.coe_of_support_subset]
    map_smul' c u := ContDiffMapSupportedIn.ext fun x ↦ by
      simp [ContDiffMapSupportedIn.coe_of_support_subset] }

variable (F) in
/-- **The Sobolev embedding into `C^k` with a fixed compact support.** For a Schwartz function `φ`
with topological support in a compact set `K` and `s > k + dim E / 2`, the bounded operator
`H^s(E, F) → 𝓓^{k}_{K}(E, F)` sending `u` to the Sobolev embedding of `φ u`
(`BesselPotentialSpace.coe_smulLeftContDiffMapSupportedIn`), a `C^k` function vanishing outside
`K`. -/
def smulLeftContDiffMapSupportedIn (hk : finrank ℝ E + 2 * k < 2 * s) (hφ : tsupport φ ⊆ K) :
    H^{s}(E, F) →L[ℂ] 𝓓^{k}_{K}(E, F) where
  toLinearMap := smulLeftContDiffMapSupportedInₗ F hk hφ
  cont := by
    have hs : finrank ℝ E < 2 * s := by linarith
    obtain ⟨C, hC, hbound⟩ := exists_norm_iteratedFDeriv_toZeroAtInfty_le (F := F) (hs := hs) hk
    set M := ‖(smulLeftCLM s φ : H^{s}(E, F) →L[ℂ] H^{s}(E, F))‖
    refine WithSeminorms.continuous_of_isBounded (norm_withSeminorms ℂ H^{s}(E, F))
      (ContDiffMapSupportedIn.withSeminorms ℂ E F k K) _
      (.of_real fun i ↦ ⟨{()}, C * M, fun u ↦ ?_⟩)
    have hCu : 0 ≤ C * M * ‖u‖ := by positivity
    refine le_of_le_of_eq ((ContDiffMapSupportedIn.seminorm_le_iff ℂ hCu i
      (smulLeftContDiffMapSupportedInₗ F hk hφ u)).2 fun hi x _ ↦ ?_) (by simp)
    calc ‖iteratedFDeriv ℝ i (toZeroAtInfty hs (smulLeftCLM s φ u)) x‖
        ≤ C * ‖smulLeftCLM s φ u‖ := hbound _ i (by exact_mod_cast hi) x
      _ ≤ C * M * ‖u‖ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left ((smulLeftCLM s φ).le_opNorm u) hC

/-- The embedding sends `u` to the Sobolev embedding of `φ u`. -/
@[simp]
theorem coe_smulLeftContDiffMapSupportedIn (hk : finrank ℝ E + 2 * k < 2 * s)
    (hφ : tsupport φ ⊆ K) (u : H^{s}(E, F)) :
    ⇑(smulLeftContDiffMapSupportedIn F hk hφ u) =
      ⇑(toZeroAtInfty (by linarith) (smulLeftCLM s φ u)) := by
  rfl

/-- **Compactness of the Sobolev embedding into `C^k` with a fixed compact support.** For a
finite-dimensional fibre `F`, a Schwartz function `φ` with topological support in a compact set `K`
and `s > k + dim E / 2`, the operator `u ↦ φ u` from `H^s(E, F)` to `𝓓^{k}_{K}(E, F)` is compact.
In particular a bounded subset of `H^s` on which multiplication by `φ` is the identity, for
instance one of elements supported in a compact set on a neighbourhood of which `φ = 1`, has
relatively compact image in `𝓓^{k}_{K}(E, F)`. -/
theorem isCompactOperator_smulLeftContDiffMapSupportedIn [FiniteDimensional ℂ F]
    (hk : finrank ℝ E + 2 * k < 2 * s) (hφ : tsupport φ ⊆ K) :
    IsCompactOperator (smulLeftContDiffMapSupportedIn F hk hφ) := by
  -- An intermediate order `r` with `k + dim E / 2 < r < s`.
  set r := (finrank ℝ E + 2 * k + 2 * s) / 4
  have hr : finrank ℝ E + 2 * k < 2 * r := by
    simp only [r]
    linarith
  have hrs : r < s := by
    simp only [r]
    linarith
  -- A cutoff `ψ` equal to `1` near the support of `φ`, so that `φ (ψ u) = φ u`.
  obtain ⟨ψ, -, -, hψ⟩ := (K.isCompact.of_isClosed_subset (isClosed_tsupport φ) hφ)
    |>.exists_schwartzMap_cutoff isOpen_univ (subset_univ _)
  have hψφ : (ψ : E → ℂ) * φ = φ := by
    ext x
    by_cases hx : x ∈ tsupport φ
    · simp [hψ.self_of_nhdsSet x hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have heq : smulLeftContDiffMapSupportedIn F hk hφ =
      smulLeftContDiffMapSupportedIn F hr hφ ∘L (inclusion hrs.le ∘L smulLeftCLM s ψ) := by
    ext u : 1
    have h : (smulLeftCLM s φ u).toDistr =
        (smulLeftCLM r φ (inclusion hrs.le (smulLeftCLM s ψ u))).toDistr := by
      simp only [toDistr_smulLeftCLM, toDistr_inclusion,
        smulLeftCLM_smulLeftCLM_apply ψ.hasTemperateGrowth φ.hasTemperateGrowth, hψφ]
    refine ContDiffMapSupportedIn.ext fun x ↦ ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      coe_smulLeftContDiffMapSupportedIn, coe_smulLeftContDiffMapSupportedIn,
      toZeroAtInfty_congr h]
  rw [heq, ContinuousLinearMap.coe_comp]
  exact (isCompactOperator_inclusion_comp_smulLeftCLM ψ hrs).clm_comp _

end BesselPotentialSpace
