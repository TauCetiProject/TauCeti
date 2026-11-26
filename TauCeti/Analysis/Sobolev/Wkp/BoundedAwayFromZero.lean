/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Zero
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Functions bounded away from zero are far from `W^{k,∞}_0`

Let `Ω` be a nonempty open subset of a finite-dimensional real inner product space `E` of
positive dimension. The zero-boundary space `W^{k,∞}_0(Ω)` is the closure of the test functions
in the full `W^{k,∞}` norm (`TauCeti.wkp0Submodule`). A test function vanishes outside a compact
subset `K` of `Ω`, and `Ω ∖ K` is a nonempty open set: otherwise `Ω = K` would be a nonempty
compact clopen set, hence all of the noncompact space `E`. So if `|u| ≥ c` almost everywhere on
`Ω`, then the value of `u - φ` has modulus at least `c` on a set of positive measure for every
test function `φ`, and its `L^∞` norm, which the `W^{k,∞}` norm dominates, is at least `c`. The
set of `v` with `c ≤ dist u v` is closed, so the bound passes to the closure of the test functions
(`TauCeti.Wkp.le_dist_of_le_abs_value`).

Constants lie in `W^{k,∞}(Ω)` for every `k`, the constant `c` with norm at most `|c|`
(`TauCeti.Wkp.exists_value_ae_eq_const`), so its distance to `W^{k,∞}_0(Ω)` is exactly `|c|`
(`TauCeti.Wkp.infDist_wkp0Submodule_eq_abs`). In particular `W^{k,∞}_0(Ω) ≠ W^{k,∞}(Ω)` for every
nonempty open `Ω` and every order `k` (`TauCeti.wkp0Submodule_ne_top`), the whole space `E`
included. This is the endpoint counterpart of `TauCeti.wkp0Submodule_top_eq_top`, by which
`W^{k,p}_0(E) = W^{k,p}(E)` for finite `p`; there the constant `1` is no counterexample, because
it is not even in `Lᵖ(E)` (`TauCeti.Wkp.not_value_ae_eq_const`). The hypothesis that `E` is
nontrivial is needed: on the zero space the constant `1` is itself a test function.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., §3, for the failure of approximation
  by test functions at the infinite exponent.
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal Distributions

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {k : ℕ}

/-- **Functions bounded away from zero are far from `W^{k,∞}_0`.** In a space of positive
dimension, if `u ∈ W^{k,∞}(Ω)` satisfies `c ≤ |u|` almost everywhere on the nonempty open set `Ω`,
then `u` is at distance at least `c` from every element of `W^{k,∞}_0(Ω)`. -/
theorem Wkp.le_dist_of_le_abs_value [Nontrivial E] (hne : (Omega : Set E).Nonempty)
    {u : Wkp mu Omega ∞ k} {c : ℝ} (hu : ∀ᵐ x ∂mu.restrict Omega, c ≤ |value k u x|)
    {v : Wkp mu Omega ∞ k} (hv : v ∈ wkp0Submodule mu Omega ∞ k) : c ≤ dist u v := by
  -- The bound is closed in `v`, so it suffices to test it on test functions.
  refine wkp0Submodule_subset_of_isClosed k
    (isClosed_le continuous_const (continuous_const.dist continuous_id)) (fun φ ↦ ?_) hv
  set w := Wkp.ofTestFunctionₗ (mu := mu) (p := ∞) k φ
  -- Outside the support of `φ` the value of `u - w` is that of `u`. That region of `Ω` is a
  -- nonempty open set, since otherwise `Ω` would be a nonempty compact clopen set, hence the whole
  -- noncompact space.
  set U := (Omega : Set E) \ tsupport φ
  have hUΩ : U ⊆ Omega := sdiff_subset
  have hUne : U.Nonempty := by
    refine sdiff_nonempty.2 fun hsub ↦ ?_
    have hΩ : (Omega : Set E) = tsupport φ := subset_antisymm hsub φ.tsupport_subset
    have huniv : (Omega : Set E) = univ :=
      IsClopen.eq_univ ⟨hΩ ▸ isClosed_tsupport _, Omega.isOpen⟩ hne
    exact noncompact_univ E (huniv ▸ hΩ ▸ φ.hasCompactSupport.isCompact)
  have : (ae (mu.restrict U)).NeBot := ae_restrict_neBot.2
    ((Omega.isOpen.sdiff (isClosed_tsupport _)).measure_ne_zero mu hUne)
  have hsub : (value k (u - w) : E → ℝ) =ᵐ[mu.restrict Omega] value k u - value k w := by
    rw [Wkp.value_sub]
    exact Lp.coeFn_sub _ _
  have hall : ∀ᵐ x ∂mu.restrict U, x ∈ U ∧ c ≤ |value k u x| ∧
      value k (u - w) x = value k u x - value k w x ∧ value k w x = φ x ∧
      ‖value k (u - w) x‖ ≤ ‖value k (u - w)‖ := by
    filter_upwards [ae_restrict_mem (Omega.isOpen.sdiff (isClosed_tsupport _)).measurableSet,
      ae_restrict_of_ae_restrict_of_subset hUΩ hu,
      ae_restrict_of_ae_restrict_of_subset hUΩ hsub,
      ae_restrict_of_ae_restrict_of_subset hUΩ (Wkp.value_ofTestFunctionₗ_ae (p := ∞) k φ),
      ae_restrict_of_ae_restrict_of_subset hUΩ (Lp.ae_norm_le_norm_top (value k (u - w)))]
      with x h₁ h₂ h₃ h₄ h₅
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  obtain ⟨x, hx, hxc, hxsub, hxw, hxle⟩ := hall.exists
  rw [hxsub, hxw, image_eq_zero_of_notMem_tsupport hx.2, sub_zero, Real.norm_eq_abs] at hxle
  have hdist : c ≤ dist u w := by
    rw [dist_eq_norm]
    exact hxc.trans (hxle.trans (Wkp.norm_value_le k (u - w)))
  exact hdist

/-- A function bounded away from zero on a nonempty open set `Ω`, in a space of positive dimension,
does not lie in `W^{k,∞}_0(Ω)`. -/
theorem Wkp.notMem_wkp0Submodule_of_le_abs_value [Nontrivial E] (hne : (Omega : Set E).Nonempty)
    {u : Wkp mu Omega ∞ k} {c : ℝ} (hc : 0 < c)
    (hu : ∀ᵐ x ∂mu.restrict Omega, c ≤ |value k u x|) : u ∉ wkp0Submodule mu Omega ∞ k :=
  fun h ↦ by simpa [hc.not_ge] using Wkp.le_dist_of_le_abs_value hne hu h

/-- **Constants are `W^{k,∞}` functions.** On every open set `Ω`, the constant function `c`
represents an element of `W^{k,∞}(Ω)` of norm at most `|c|`. -/
theorem Wkp.exists_value_ae_eq_const (k : ℕ) (c : ℝ) :
    ∃ u : Wkp mu Omega ∞ k, (value k u : E → ℝ) =ᵐ[mu.restrict Omega] (fun _ ↦ c) ∧ ‖u‖ ≤ |c| := by
  have hf : ContDiffOn ℝ k (fun _ : E ↦ c) Omega := contDiffOn_const
  obtain ⟨u, hu⟩ := Wkp.exists_value_ae_eq_of_contDiffOn (mu := mu) (p := ∞) k hf fun i _ ↦ by
    rcases eq_or_ne i 0 with rfl | hi
    · rw [iteratedFDeriv_zero_eq_comp]
      exact memLp_top_const _
    · rw [iteratedFDeriv_const_of_ne hi]
      exact memLp_top_const _
  refine ⟨u, hu, ?_⟩
  rcases (Omega : Set E).eq_empty_or_nonempty with hempty | hne
  · rw [Subsingleton.elim u 0 (h := Wkp.subsingleton_of_eq_empty k hempty), norm_zero]
    exact abs_nonneg c
  have hμ : mu.restrict Omega ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    exact Omega.isOpen.measure_ne_zero mu hne
  -- The jet of `c` is `c` in degree zero and `0` in every positive degree, so the sum of the
  -- `L^∞` norms of its components is `|c|`.
  have hjet : ∀ i, lpNorm (iteratedFDeriv ℝ i fun _ : E ↦ c) ∞ (mu.restrict Omega) =
      if i = 0 then |c| else 0 := fun i ↦ by
    split_ifs with hi
    · subst hi
      rw [iteratedFDeriv_zero_eq_comp]
      simp [Function.comp_def, lpNorm_const ENNReal.top_ne_zero hμ]
    · simp [iteratedFDeriv_const_of_ne hi]
  refine (Wkp.norm_le_sum_lpNorm_iteratedFDeriv_of_contDiffOn k u hf hu).trans_eq ?_
  simp [hjet, Finset.sum_ite_eq']

/-- **A constant is at distance exactly its modulus from `W^{k,∞}_0(Ω)`.** On a nonempty open set
in a space of positive dimension, every `u ∈ W^{k,∞}(Ω)` represented by the constant `c` has
`infDist u W^{k,∞}_0(Ω) = |c|`. -/
theorem Wkp.infDist_wkp0Submodule_eq_abs [Nontrivial E] (hne : (Omega : Set E).Nonempty)
    {u : Wkp mu Omega ∞ k} {c : ℝ} (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] fun _ ↦ c) :
    infDist u (wkp0Submodule mu Omega ∞ k : Set (Wkp mu Omega ∞ k)) = |c| := by
  have h0 : (0 : Wkp mu Omega ∞ k) ∈ wkp0Submodule mu Omega ∞ k := zero_mem _
  refine le_antisymm ((infDist_le_dist_of_mem h0).trans ?_)
    ((le_infDist ⟨0, h0⟩).2 fun v hv ↦ Wkp.le_dist_of_le_abs_value hne
      (hu.mono fun x hx ↦ hx.symm ▸ le_rfl) hv)
  obtain ⟨u', hu', hnorm⟩ := Wkp.exists_value_ae_eq_const (mu := mu) (Omega := Omega) k c
  rw [dist_zero_right, Wkp.ext k (Lp.ext (hu.trans hu'.symm))]
  exact hnorm

/-- **`W^{k,∞}_0(Ω) ≠ W^{k,∞}(Ω)`.** On every nonempty open set `Ω` in a space of positive
dimension, including the whole space, the closure of the test functions in `W^{k,∞}(Ω)` is a
proper subspace: it misses the constant `1`. -/
theorem wkp0Submodule_ne_top [Nontrivial E] (hne : (Omega : Set E).Nonempty) (k : ℕ) :
    wkp0Submodule mu Omega ∞ k ≠ ⊤ := by
  obtain ⟨u, hu, -⟩ := Wkp.exists_value_ae_eq_const (mu := mu) (Omega := Omega) k 1
  refine fun h ↦ Wkp.notMem_wkp0Submodule_of_le_abs_value hne one_pos
    (hu.mono fun x hx ↦ by rw [hx, abs_one]) ?_
  rw [h]
  exact ClosedSubmodule.mem_top

/-- **For finite `p` no nonzero constant is a Sobolev function on the whole space.** In a space of
positive dimension, no `u ∈ W^{k,p}(E)` with `p < ∞` is represented by a constant `c ≠ 0`, since
the Haar measure of `E` is infinite. -/
theorem Wkp.not_value_ae_eq_const [Nontrivial E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : Wkp mu ⊤ p k) {c : ℝ} (hc : c ≠ 0) : ¬(value k u : E → ℝ) =ᵐ[mu] fun _ ↦ c :=
  fun hu ↦ by
    have hmem : MemLp (fun _ : E ↦ c) p mu := (Wkp.memLp_value k u).ae_eq hu
    rw [memLp_const_iff (zero_lt_one.trans_le Fact.out).ne' hp] at hmem
    simp [hc, measure_univ_of_isAddLeftInvariant mu] at hmem

end TauCeti
