/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Little
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Paraproduct
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# Density of the Schwartz functions in the Besov spaces `B^s_{p,q}`, `q < ∞`

For a finite fine index `q`, an element `u` of the inhomogeneous Besov space `B^s_{p,q}` is the
limit of its low-frequency cut-offs `S_m u = ∑_{k < m} Δₖ u` (`TauCeti.BesovSpace.lowPass`), and
it lies in the closure of the Schwartz functions exactly when each of its Littlewood–Paley blocks
`Δⱼ u` is an `Lᵖ` limit of Schwartz functions
(`TauCeti.BesovSpace.mem_closure_range_toBesovSpaceCLM_iff`). For `p < ∞` the second condition
always holds, so the Schwartz functions are dense in `B^s_{p,q}` whenever `p, q < ∞`
(`SchwartzMap.denseRange_toBesovSpaceCLM`). A continuous linear map out of such a Besov space,
for instance a functional in its dual, is therefore determined by its values on the Schwartz
functions. This is the uniqueness half of the identification of the dual of `B^s_{p,q}` with
`B^{-s}_{p',q'}` through the pairing with Schwartz functions.

Both finiteness conditions are needed. For `q = ∞` the closure of the Schwartz functions is the
little Besov space `b^s_{p,∞}` (`TauCeti.BesovSpace.littleBesov`), cut out by the decay
`2^{js} ‖Δⱼ u‖_p → 0`, which a general element of `B^s_{p,∞}` does not have. For `p = ∞` the
closure of the Schwartz functions in `L^∞` consists of continuous functions vanishing at infinity,
and the constant function `1`, whose block `Δ₀ 1` is `1`, is not of this kind.

## The argument

Each `S_m u` is an `Lᵖ` function whose blocks vanish from index `m + L` on, where `L` is the
almost-orthogonality range of the blocks, so it lies in every Besov space built on `Lᵖ`
(`TauCeti.BesovSpace.memBesov_lowPass`). Since the blocks commute, the block `Δₖ (u - S_m u)` is
`Δₖ u - S_m Δₖ u`. It vanishes for `k + L < m`, and in general it has `Lᵖ` norm at most `(1 + K)`
times `‖Δₖ u‖_p`, where `K` bounds the low-frequency cut-offs on `Lᵖ` uniformly in `m`. Hence
the weighted blocks of `u - S_m u` are bounded by `(1 + K)` times the tail from index `m - L` on
of the sequence `(2^{ks} ‖Δₖ u‖_p)ₖ ∈ ℓ^q`, and for `q < ∞` these tails tend to zero in `ℓ^q`
(`lp.hasSum_single`). This gives `S_m u → u` in `B^s_{p,q}`
(`TauCeti.BesovSpace.tendsto_of_toDistr_eq_lowPass`).

If the blocks of `u` are `Lᵖ` limits of Schwartz functions, so is the finite sum `S_m u`; being
band-limited, it lies in the little Besov space `b^{s+1}_{p,∞}`
(`TauCeti.BesovSpace.mem_littleBesov_of_toDistr_eq`), the closure of the Schwartz functions in
`B^{s+1}_{p,∞}`. The continuous inclusion `B^{s+1}_{p,∞} ⊆ B^s_{p,q}` maps it into the closure of
the Schwartz functions in `B^s_{p,q}`, and so does the limit `u` of the `S_m u`.

## Main declarations

* `TauCeti.BesovSpace.tendsto_of_toDistr_eq_lowPass`: for `q < ∞`, `S_m u → u` in `B^s_{p,q}`.
* `TauCeti.BesovSpace.mem_closure_range_toBesovSpaceCLM_iff`: for `q < ∞`, `u` is a limit of
  Schwartz functions in `B^s_{p,q}` exactly when its blocks are limits of Schwartz functions in
  `Lᵖ`.
* `SchwartzMap.denseRange_toBesovSpaceCLM`: for `p, q < ∞`, the Schwartz functions are dense in
  `B^s_{p,q}`.

## References

* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, Section 2.3.3.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Section 2.7.
-/

public section

noncomputable section

open Filter Topology MeasureTheory FourierTransform TemperedDistribution
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti

namespace BesovSpace

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

variable [Fact (1 ≤ q)]

/-- **The weighted blocks of `u - S_m u` lie below a tail of those of `u`.** With `L` the
almost-orthogonality range of the blocks and `K = ‖𝓕⁻ φ‖₁`, for every `v` with tempered
distribution `S_{N+1} u` the norm `‖u - v‖` is at most `(1 + K)` times the `ℓ^q` norm of the tail
from index `N + 1 - L` on of the sequence `a = (2^{ks} ‖Δₖ u‖_p)ₖ`. -/
private theorem exists_norm_sub_le_norm_tail (u : BesovSpace F φ s p q) :
    ∃ (L : ℕ) (K : ℝ) (a : lp (fun _ : ℕ ↦ ℝ) q),
      ∀ (N : ℕ) (v : BesovSpace F φ s p q), v.toDistr = u.lowPass (N + 1) →
        ‖u - v‖ ≤ (1 + K) *
          ‖a - ∑ i ∈ Finset.range (N + 1 - L), lp.single q i (a i)‖ := by
  obtain ⟨L, hL⟩ := exists_block_sub_eq_zero_and_norm_le_of_toDistr_eq_lowPass (F := F) (φ := φ)
  set K : ℝ := ∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖
  have hK0 : 0 ≤ K := integral_nonneg fun _ ↦ norm_nonneg _
  obtain ⟨a, ha, -⟩ := exists_lp_eq_rpow_mul_norm_block_and_norm_le u
  refine ⟨L, K, a, fun N v hv ↦ ?_⟩
  set n := N + 1 - L
  set t : lp (fun _ : ℕ ↦ ℝ) q := a - ∑ i ∈ Finset.range n, lp.single q i (a i)
  have ht (k : ℕ) : t k = if n ≤ k then a k else 0 := by
    simp only [t, lp.coeFn_sub, lp.coeFn_sum, lp.coeFn_single, Pi.sub_apply, Finset.sum_apply,
      Finset.sum_pi_single, Finset.mem_range]
    by_cases h : n ≤ k
    · simp [h, Nat.not_lt.2 h]
    · simp [h, Nat.lt_of_not_le h]
  -- The weighted blocks of `u - v` are bounded by the tail `(1 + K) t`.
  obtain ⟨x, hx, hxb⟩ := exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_eq
    (u - v).block ((1 + K) • t) (fun k ↦ (coe_block (u - v) k).symm) fun k ↦ by
      rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ht]
      obtain ⟨h0, hle⟩ := hL u v N k hv
      rcases le_or_gt (k + L) N with hkN | hkN
      · -- Low frequencies: the block of `u - v` vanishes.
        have hak : 0 ≤ a k := by rw [ha]; positivity
        rw [h0 hkN, norm_zero, mul_zero]
        exact mul_nonneg (by linarith) (by split_ifs <;> simp [hak])
      · -- High frequencies: the weighted block of `u - v` is at most `(1 + K)` times that of `u`.
        simp only [show n ≤ k by omega, ↓reduceIte, ha]
        calc 2 ^ (s * k) * ‖(u - v).block k‖ ≤ 2 ^ (s * k) * ((1 + K) * ‖u.block k‖) := by
              gcongr
          _ = (1 + K) * (2 ^ (s * k) * ‖u.block k‖) := by ring
  rw [ext hx, norm_smul, Real.norm_of_nonneg (by linarith)] at hxb
  exact hxb

/-- **An element of `B^s_{p,q}`, `q < ∞`, is the limit of its low-frequency cut-offs.** If
`v m ∈ B^s_{p,q}` has the tempered distribution `S_m u = ∑_{k < m} Δₖ u` for every `m`, then
`v m → u` in `B^s_{p,q}`. Such `v m` exist by `TauCeti.BesovSpace.memBesov_lowPass`. -/
theorem tendsto_of_toDistr_eq_lowPass (hq : q ≠ ∞) {u : BesovSpace F φ s p q}
    {v : ℕ → BesovSpace F φ s p q} (hv : ∀ m, (v m).toDistr = u.lowPass m) :
    Tendsto v atTop (𝓝 u) := by
  obtain ⟨L, K, a, hle⟩ := exists_norm_sub_le_norm_tail u
  -- The tails of `a ∈ ℓ^q` tend to zero, since `a` is the sum of its coordinates.
  have htail : Tendsto (fun n : ℕ ↦ a - ∑ i ∈ Finset.range n, lp.single q i (a i))
      atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := a)).sub (lp.hasSum_single hq a).tendsto_sum_nat
    rwa [sub_self] at h
  have hn : Tendsto (fun N : ℕ ↦ N + 1 - L) atTop atTop :=
    (tendsto_sub_atTop_nat L).comp (tendsto_add_atTop_nat 1)
  rw [← tendsto_add_atTop_iff_nat 1, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun N ↦ ?_)
    (by simpa using ((htail.comp hn).norm.const_mul (1 + K)))
  rw [norm_sub_rev]
  exact hle N (v (N + 1)) (hv (N + 1))

/-- **The closure of the Schwartz functions in `B^s_{p,q}`, `q < ∞`, is cut out by the blocks:**
`u` is a limit of Schwartz functions in `B^s_{p,q}` exactly when every block `Δⱼ u` is a limit of
Schwartz functions in `Lᵖ`. For `q = ∞` the closure is the little Besov space, which also requires
the decay `2^{js} ‖Δⱼ u‖_p → 0` (`TauCeti.BesovSpace.mem_littleBesov_iff`). -/
theorem mem_closure_range_toBesovSpaceCLM_iff (hq : q ≠ ∞) {u : BesovSpace F φ s p q} :
    u ∈ closure (Set.range (SchwartzMap.toBesovSpaceCLM F φ s p q)) ↔
      ∀ j, u.block j ∈ closure (Set.range fun f : 𝓢(E, F) ↦ f.toLp p) := by
  refine ⟨fun hu j ↦ ?_, fun hblock ↦ ?_⟩
  · refine map_mem_closure (f := fun x : BesovSpace F φ s p q ↦ x.block j) (continuous_block j)
      hu ?_
    rintro _ ⟨f, rfl⟩
    exact ⟨_, (block_toBesovSpaceCLM f j).symm⟩
  obtain ⟨L, hL⟩ := exists_littlewoodPaleyBlock_lowPass_eq_zero (F := F) (φ := φ)
  obtain ⟨C, -, hC⟩ := exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_eq_zero F φ
  -- The `Lᵖ` closure of the Schwartz functions is a subspace.
  have hS := SchwartzMap.closure_range_toLp_eq (F := F) (μ := (volume : Measure E)) p
  -- Each low-frequency cut-off is a limit of Schwartz functions in `B^s_{p,q}`.
  have hmem (m : ℕ) : ∃ v ∈ closure (Set.range (SchwartzMap.toBesovSpaceCLM F φ s p q)),
      v.toDistr = u.lowPass m := by
    have hw : u.lowPass m ∈ closure (Set.range fun f : 𝓢(E, F) ↦ f.toLp p) := by
      rw [hS, lowPass_eq_sum]
      exact Submodule.sum_mem _ fun j _ ↦ by rw [← SetLike.mem_coe, ← hS]; exact hblock j
    -- As a band-limited `Lᵖ` limit of Schwartz functions, `S_m u` lies in `b^{s+1}_{p,∞}`.
    obtain ⟨x, hx, -⟩ := hC (s + 1) (m + L) (u.lowPass m) fun k hk ↦ hL u m k hk
    have hxl := mem_littleBesov_of_toDistr_eq hx hw fun k hk ↦ hL u m k hk
    rw [← SetLike.mem_coe, coe_littleBesov] at hxl
    refine ⟨inclusionOfLT F φ p ∞ q (lt_add_one s) x,
      map_mem_closure (inclusionOfLT F φ p ∞ q (lt_add_one s)).continuous hxl ?_,
      by rw [toDistr_inclusionOfLT, hx]⟩
    rintro _ ⟨f, rfl⟩
    exact ⟨f, ext (by simp only [toDistr_inclusionOfLT, SchwartzMap.toDistr_toBesovSpaceCLM])⟩
  choose v hvS hv using hmem
  exact isClosed_closure.mem_of_tendsto (tendsto_of_toDistr_eq_lowPass hq hv)
    (Eventually.of_forall hvS)

end BesovSpace

end TauCeti

namespace SchwartzMap

open TauCeti

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **The Schwartz functions are dense in `B^s_{p,q}` for `p, q < ∞`.** -/
theorem denseRange_toBesovSpaceCLM (hp : p ≠ ∞) (hq : q ≠ ∞) :
    DenseRange (toBesovSpaceCLM F φ s p q) := fun u ↦
  (BesovSpace.mem_closure_range_toBesovSpaceCLM_iff hq).2 fun j ↦
    denseRange_toLpCLM (F := F) (μ := (volume : Measure E)) hp (u.block j)

end SchwartzMap
