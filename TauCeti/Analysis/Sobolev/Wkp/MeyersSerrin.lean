/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Extension
public import TauCeti.Analysis.Sobolev.Wkp.LocalApproximation
public import TauCeti.Analysis.Sobolev.Wkp.Multiplication
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Smooth functions are dense in `W^{k,p}(Ω)` (Meyers–Serrin)

For `1 ≤ p < ∞`, every natural order `k`, and an **arbitrary** open set `Ω` of a
finite-dimensional real inner product space, the elements of `W^{k,p}(Ω)` with a representative
which is smooth on `Ω` are dense in `W^{k,p}(Ω)`, in the full Sobolev norm. In other words
`H = W`: the closure of `C^∞(Ω) ∩ W^{k,p}(Ω)` is all of `W^{k,p}(Ω)`. No boundedness and no
regularity of the boundary of `Ω` is assumed.

The approximants are smooth on `Ω` but need not be smooth up to its boundary, nor compactly
supported in `Ω`: on standard nontrivial bounded domains (for example, Euclidean balls in positive
dimension), `W^{k,p}_0(Ω)` is a proper subspace for `k ≥ 1`, so test functions are not dense. On
the whole space, density of globally smooth representatives is
`TauCeti.Wkp.dense_contDiff_representatives`.

## Cutoffs

The proof localizes `u` by a decomposition of unity, which needs the product `ζ u` of `u` with a
smooth function `ζ` compactly supported in `Ω`. This file shows that such a product is a
`W^{k,p}_0(Ω)` function (`TauCeti.Wkp.exists_mem_wkp0Submodule_value_ae_eq_mul`). Take an open
`U` with compact closure in `Ω` containing the support of `ζ`, and test functions `ψ n` on `Ω`
whose restrictions converge to `u` in `W^{k,p}(U)`
(`TauCeti.Wkp.exists_testFunction_approximation_restrictL`). The Leibniz estimate
`TauCeti.Wkp.norm_ofTestFunctionₗ_le_of_eqOn_mul` on `U` bounds the `W^{k,p}` norm of the test
function `ζ (ψ n - ψ m)` by that of `ψ n - ψ m` on `U`, and extension by zero from `U` to `Ω`
preserves it. So the test functions `ζ ψ n` converge in `W^{k,p}(Ω)`, and their limit has value
`ζ u`.

## The gluing

Take a decomposition of unity `(ζ j)` of `Ω` by test functions, together with cutoffs `χ j` equal
to one on the support of `ζ j` and locally finite in `Ω`
(`IsOpen.exists_contDiff_decomposition_cutoff`). Each piece `ζ j u` is approximated, to within
`ε 2^{-j}`, by a test function `ζ j ψ j`, which vanishes wherever `χ j` does. The sum
`f = ∑ j, ζ j ψ j` is locally finite in `Ω`, hence smooth there.

The series `∑ j, ζ j u` need not converge to `u` in `W^{k,p}(Ω)`, so the comparison with `u` is
made through the corrections instead. These are absolutely summable in the Banach space
`W^{k,p}(Ω)`, to some `w` of norm at most `ε / 2`; after passing to a subsequence,
representatives of their partial sums converge almost everywhere on `Ω` to `f - u`. Hence
`u + w` is within `ε` of `u`, and its value is represented by `f`.

## Main declarations

* `TauCeti.Wkp.exists_mem_wkp0Submodule_value_ae_eq_mul`: the product of a `W^{k,p}(Ω)` function
  with a smooth function compactly supported in `Ω` lies in `W^{k,p}_0(Ω)`.
* `TauCeti.Wkp.exists_contDiffOn_approximation`: every `u ∈ W^{k,p}(Ω)` is a Sobolev-norm limit of
  elements with representatives smooth on `Ω`.
* `TauCeti.Wkp.dense_contDiffOn_representatives`: those elements are dense in `W^{k,p}(Ω)`.

## References

* N. G. Meyers, J. Serrin, *H = W*, Proc. Nat. Acad. Sci. U.S.A. 51 (1964), 1055–1056.
* L. C. Evans, *Partial Differential Equations*, §5.3.2, Theorem 2.
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace TauCeti.Wkp

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- The cutoff `ζ u` of `u ∈ W^{k,p}(Ω)` by a smooth `ζ` compactly supported in `Ω` is a
`W^{k,p}(Ω)` limit of test functions `ζ ψ n`, which vanish wherever `ζ` does. -/
private theorem exists_tendsto_ofTestFunctionₗ_mul (hp : p ≠ ⊤) {zeta : E → ℝ}
    (hzeta : ContDiff ℝ ∞ zeta) (hcpt : HasCompactSupport zeta)
    (hts : tsupport zeta ⊆ Omega) (k : ℕ) (u : Wkp mu Omega p k) :
    ∃ (v : Wkp mu Omega p k) (Phi : ℕ → 𝓓(Omega, ℝ)), (∀ n x, zeta x = 0 → Phi n x = 0) ∧
      (value k v : E → ℝ) =ᵐ[mu.restrict Omega] (fun x => zeta x * value k u x) ∧
      Tendsto (fun n => ofTestFunctionₗ (mu := mu) (p := p) k (Phi n)) atTop (𝓝 v) := by
  obtain ⟨V, hVo, hKV, hVcl, hVc⟩ :=
    exists_open_between_and_isCompact_closure hcpt Omega.isOpen hts
  let U : Opens E := ⟨V, hVo⟩
  have hUO : U ≤ Omega := SetLike.coe_subset_coe.mp (subset_closure.trans hVcl)
  obtain ⟨psi, hpsi⟩ :=
    exists_testFunction_approximation_restrictL (U := U) hp hVc hVcl k u
  -- a common bound for the derivatives of `ζ` through order `k`
  choose C hC using fun i : ℕ => Continuous.bounded_above_of_compact_support
    (hzeta.continuous_iteratedFDeriv (m := i) (by simp)) (hcpt.iteratedFDeriv i)
  set M := ∑ i ∈ Finset.range (k + 1), |C i|
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hM : ∀ i ≤ k, ∀ x ∈ U, ‖iteratedFDeriv ℝ i zeta x‖ ≤ M := fun i hi x _ =>
    (hC i x).trans ((le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (C j))
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))))
  -- the test functions `ζ ψ n` on `U`, and the same functions on `Ω`
  let PhiU : ℕ → 𝓓(U, ℝ) := fun n => ⟨zeta * (psi n : E → ℝ), hzeta.mul (psi n).contDiff,
    (psi n).hasCompactSupport.mul_left, tsupport_mul_subset_left.trans hKV⟩
  let Phi : ℕ → 𝓓(Omega, ℝ) := fun n => TestFunction.monoCLM ℝ (PhiU n)
  have hPhi : ∀ n x, Phi n x = zeta x * psi n x := fun n x => by
    simp [Phi, PhiU, hUO]
  -- extension by zero from `U` to `Ω` preserves the norm of the test functions
  have hnorm : ∀ n m, ‖ofTestFunctionₗ (mu := mu) (p := p) k (Phi n) -
      ofTestFunctionₗ k (Phi m)‖ = ‖ofTestFunctionₗ (mu := mu) (p := p) k (PhiU n - PhiU m)‖ := by
    intro n m
    have h := (Wkp0.extendByZeroₗᵢ (mu := mu) (p := p) hUO k).norm_map
      (Wkp0.ofTestFunctionₗ k (PhiU n - PhiU m))
    rw [Wkp0.extendByZeroₗᵢ_ofTestFunctionₗ, map_sub, ← Submodule.norm_coe,
      ← Submodule.norm_coe, Wkp0.coe_ofTestFunctionₗ, Wkp0.coe_ofTestFunctionₗ] at h
    rwa [← map_sub]
  -- the restrictions of the `ψ n` to `U`, which converge to the restriction of `u`
  let r : ℕ → Wkp mu U p k := fun n => restrictL hUO k (ofTestFunctionₗ (mu := mu) (p := p) k
    (psi n))
  have hr : ∀ n, (value k (r n) : E → ℝ) =ᵐ[mu.restrict U] psi n := fun n => by
    have hmono : ae (mu.restrict (U : Set E)) ≤ ae (mu.restrict (Omega : Set E)) :=
      ae_mono (Measure.restrict_mono (SetLike.coe_subset_coe.mpr hUO) le_rfl)
    filter_upwards [value_restrictL_ae hUO k (ofTestFunctionₗ (mu := mu) (p := p) k (psi n)),
      (testFunctionLp_apply_ae (mu := mu) p (psi n)).filter_mono hmono] with x h1 h2
    rw [h1, value_ofTestFunctionₗ, h2]
  -- the Leibniz estimate makes the test functions `ζ ψ n` a Cauchy sequence in `W^{k,p}(Ω)`
  have hest : ∀ n m, ‖ofTestFunctionₗ (mu := mu) (p := p) k (Phi n) -
      ofTestFunctionₗ k (Phi m)‖ ≤ 2 ^ (k + 1) * M * ‖r n - r m‖ := by
    intro n m
    rw [hnorm]
    refine norm_ofTestFunctionₗ_le_of_eqOn_mul k hzeta hM0 hM (r n - r m)
      (f := fun x => psi n x - psi m x)
      ((((psi n).contDiff.sub (psi m).contDiff).of_le (by simp)).contDiffOn) ?_ _
      (fun x _ => by simp [PhiU, mul_sub])
    rw [← valueL_apply, map_sub, valueL_apply, valueL_apply]
    filter_upwards [Lp.coeFn_sub (value k (r n)) (value k (r m)), hr n, hr m] with x h h1 h2
    rw [h, Pi.sub_apply, h1, h2]
  have hcauchy : CauchySeq fun n => ofTestFunctionₗ (mu := mu) (p := p) k (Phi n) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hpsi.cauchySeq (ε / (2 ^ (k + 1) * M + 1))
      (by positivity)
    refine ⟨N, fun n hn m hm => ?_⟩
    have hnm := hN n hn m hm
    rw [dist_eq_norm] at hnm ⊢
    calc _ ≤ 2 ^ (k + 1) * M * ‖r n - r m‖ := hest n m
      _ ≤ (2 ^ (k + 1) * M + 1) * ‖r n - r m‖ := by gcongr; linarith
      _ < (2 ^ (k + 1) * M + 1) * (ε / (2 ^ (k + 1) * M + 1)) := by gcongr
      _ = ε := by field_simp
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨v, Phi, fun n x hx => by rw [hPhi, hx, zero_mul], ?_, hv⟩
  -- identify the value of the limit through almost everywhere convergent subsequences
  have hres : Tendsto (fun n => value k (r n)) atTop (𝓝 (value k (restrictL hUO k u))) := by
    simpa only [Function.comp_def, valueL_apply] using
      ((valueL (mu := mu) (Omega := U) (p := p) k).continuous.tendsto _).comp hpsi
  have hval : Tendsto (fun n => value k (ofTestFunctionₗ (mu := mu) (p := p) k (Phi n))) atTop
      (𝓝 (value k v)) := by
    simpa only [Function.comp_def, valueL_apply] using
      ((valueL (mu := mu) (Omega := Omega) (p := p) k).continuous.tendsto v).comp hv
  obtain ⟨ns, hns, h1⟩ := (tendstoInMeasure_of_tendsto_Lp hres).exists_seq_tendsto_ae
  obtain ⟨ms, hms, h2⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hval.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have hU : ∀ᵐ x ∂mu.restrict Omega, x ∈ U →
      Tendsto (fun j => psi (ns j) x) atTop (𝓝 (value k u x)) := by
    have h : ∀ᵐ x ∂mu.restrict U, Tendsto (fun j => psi (ns j) x) atTop (𝓝 (value k u x)) := by
      filter_upwards [h1, value_restrictL_ae hUO k u, ae_all_iff.2 hr] with x hx hux hrx
      simpa only [hux, hrx] using hx
    exact ae_restrict_of_ae ((ae_restrict_iff' U.isOpen.measurableSet).1 h)
  have hPhi_ae : ∀ᵐ x ∂mu.restrict Omega, ∀ n,
      value k (ofTestFunctionₗ (mu := mu) (p := p) k (Phi n)) x = zeta x * psi n x := by
    refine ae_all_iff.2 fun n => ?_
    filter_upwards [testFunctionLp_apply_ae (mu := mu) p (Phi n)] with x hx
    rw [value_ofTestFunctionₗ, hx, hPhi]
  filter_upwards [h2, hU, hPhi_ae] with x hx hxU hPx
  simp only [Function.comp_def, hPx] at hx
  by_cases hxV : x ∈ U
  · exact tendsto_nhds_unique hx
      ((tendsto_const_nhds (x := zeta x)).mul ((hxU hxV).comp hms.tendsto_atTop))
  · have hz : zeta x = 0 := image_eq_zero_of_notMem_tsupport fun h => hxV (hKV h)
    simp only [hz, zero_mul] at hx ⊢
    exact tendsto_nhds_unique hx tendsto_const_nhds

/-- **Cutoffs of Sobolev functions have zero boundary values.** If `1 ≤ p < ∞`, `u ∈ W^{k,p}(Ω)`
and `ζ` is smooth with compact support inside `Ω`, then the product `ζ u` lies in
`W^{k,p}_0(Ω)`: some element of `W^{k,p}_0(Ω)` has value `ζ u` almost everywhere on `Ω`. No
regularity of `Ω` is assumed. -/
theorem exists_mem_wkp0Submodule_value_ae_eq_mul (hp : p ≠ ⊤) {zeta : E → ℝ}
    (hzeta : ContDiff ℝ ∞ zeta) (hcpt : HasCompactSupport zeta)
    (hts : tsupport zeta ⊆ Omega) (k : ℕ) (u : Wkp mu Omega p k) :
    ∃ v ∈ wkp0Submodule mu Omega p k,
      (value k v : E → ℝ) =ᵐ[mu.restrict Omega] (fun x => zeta x * value k u x) := by
  obtain ⟨v, Phi, -, hval, hlim⟩ := exists_tendsto_ofTestFunctionₗ_mul hp hzeta hcpt hts k u
  exact ⟨v, (wkp0Submodule mu Omega p k).isClosed.mem_of_tendsto hlim
    (Eventually.of_forall fun n => ofTestFunctionₗ_mem_wkp0Submodule k (Phi n)), hval⟩

/-- Every `u ∈ W^{k,p}(Ω)`, `p < ∞`, is within `ε` of an element whose value is represented by a
function smooth on `Ω`. -/
private theorem exists_contDiffOn_norm_sub_lt (hp : p ≠ ⊤) (k : ℕ) (u : Wkp mu Omega p k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (v : Wkp mu Omega p k) (f : E → ℝ), ContDiffOn ℝ ∞ f Omega ∧
      (value k v : E → ℝ) =ᵐ[mu.restrict Omega] f ∧ ‖v - u‖ < ε := by
  obtain ⟨zeta, chi, hzeta, hchi, hchi_one, hfin⟩ :=
    IsOpen.exists_contDiff_decomposition_cutoff Omega.isOpen
  -- the localized pieces `b j = ζ_j u`, and test functions `ζ_j ψ_j` within `ε 2^{-j-2}` of them
  choose b Phi hPhi_zero hb hlim using fun j =>
    exists_tendsto_ofTestFunctionₗ_mul hp (hzeta j).1 (hzeta j).2.1 (hzeta j).2.2 k u
  choose n hn using fun j => ((tendsto_iff_norm_sub_tendsto_zero.1 (hlim j)).eventually
    (Iic_mem_nhds (by positivity : (0 : ℝ) < ε / 4 * (1 / 2) ^ j))).exists
  let Psi : ℕ → 𝓓(Omega, ℝ) := fun j => Phi j (n j)
  have hPsi_zero : ∀ j y, chi j y = 0 → Psi j y = 0 := fun j y hy => by
    refine hPhi_zero j (n j) y (image_eq_zero_of_notMem_tsupport fun h => ?_)
    simp [hchi_one j h] at hy
  let a : ℕ → Wkp mu Omega p k := fun j => ofTestFunctionₗ (mu := mu) (p := p) k (Psi j)
  have hab : ∀ j, ‖a j - b j‖ ≤ ε / 4 * (1 / 2) ^ j := hn
  -- the corrections `a j - b j` are absolutely summable, with total norm at most `ε / 2`
  have hgeom : HasSum (fun j : ℕ => ε / 4 * (1 / 2) ^ j) (ε / 2) := by
    convert (hasSum_geometric_two).mul_left (ε / 4) using 1
    ring
  have hsummable : Summable fun j => a j - b j := hgeom.summable.of_norm_bounded hab
  set w := ∑' j, (a j - b j)
  have hw : ‖w‖ ≤ ε / 2 := tsum_of_norm_bounded hgeom hab
  -- the smooth function: a locally finite sum of test functions
  let f : E → ℝ := fun x => ∑' j, Psi j x
  have hf : ContDiffOn ℝ ∞ f Omega := fun x hx => by
    obtain ⟨m, hm⟩ := hfin x hx
    refine (contDiffAt_tsum_of_eventually_eq_zero (Finset.range m)
      (fun j _ => (Psi j).contDiff.contDiffAt) (hm.mono fun y hy j hj => ?_)).contDiffWithinAt
    exact hPsi_zero j y (hy.1 j (by simpa using hj))
  -- at each point of `Ω`, the partial sums of `Psi` and `zeta` are eventually `f` and `1`
  have hf_local : ∀ x ∈ Omega, ∃ m, ∀ N, m ≤ N →
      ∑ j ∈ Finset.range N, Psi j x = f x ∧ ∑ j ∈ Finset.range N, zeta j x = 1 := by
    intro x hx
    obtain ⟨m, hm⟩ := hfin x hx
    refine ⟨m, fun N hN => ⟨(tsum_eq_sum fun j hj => ?_).symm, hm.self_of_nhds.2 N hN⟩⟩
    exact hPsi_zero j x (hm.self_of_nhds.1 j (by simp at hj; omega))
  -- identify the `Lᵖ` limit of the partial sums with their pointwise limit `f - u`
  let S : ℕ → Wkp mu Omega p k := fun N => ∑ j ∈ Finset.range N, (a j - b j)
  have hSv : Tendsto (fun N => value k (S N)) atTop (𝓝 (value k w)) := by
    simpa only [Function.comp_def, valueL_apply] using
      ((valueL (mu := mu) (Omega := Omega) (p := p) k).continuous.tendsto w).comp
        hsummable.hasSum.tendsto_sum_nat
  obtain ⟨ns, hns, hSlim⟩ := (tendstoInMeasure_of_tendsto_Lp hSv).exists_seq_tendsto_ae
  have hpartial : ∀ᵐ x ∂mu.restrict Omega, ∀ N,
      value k (S N) x = ∑ j ∈ Finset.range N, (Psi j x - zeta j x * value k u x) := by
    rw [ae_all_iff]
    intro N
    have hS : value k (S N) = ∑ j ∈ Finset.range N, (value k (a j) - value k (b j)) := by
      simp only [S, ← valueL_apply, map_sum, map_sub]
    filter_upwards [Lp.coeFn_finsetSum (Finset.range N) fun j => value k (a j) - value k (b j),
      ae_all_iff.2 fun j => Lp.coeFn_sub (value k (a j)) (value k (b j)), ae_all_iff.2 hb,
      ae_all_iff.2 fun j => testFunctionLp_apply_ae (mu := mu) p (Psi j)] with x hx hsub hbx ha
    rw [hS, hx, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsub j, Pi.sub_apply, hbx j, value_ofTestFunctionₗ, ha j]
  have hw_ae : ∀ᵐ x ∂mu.restrict Omega, value k w x = f x - value k u x := by
    filter_upwards [hSlim, hpartial, ae_restrict_mem Omega.isOpen.measurableSet]
      with x hx hpx hxΩ
    obtain ⟨m, hm⟩ := hf_local x hxΩ
    have hconv : Tendsto (fun N => value k (S N) x) atTop (𝓝 (f x - value k u x)) := by
      refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨m, fun N hN => Eq.symm ?_⟩)
      beta_reduce
      obtain ⟨hf_eq, hz_eq⟩ := hm N hN
      rw [hpx, Finset.sum_sub_distrib, ← Finset.sum_mul, hf_eq, hz_eq, one_mul]
    exact tendsto_nhds_unique hx (hconv.comp hns.tendsto_atTop)
  refine ⟨u + w, f, hf, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_add (value k u) (value k w), hw_ae] with x hx hwx
    rw [value_add, hx, Pi.add_apply, hwx, add_sub_cancel]
  · rw [add_sub_cancel_left]
    linarith

/-- **Meyers–Serrin approximation in `W^{k,p}(Ω)`.** For `1 ≤ p < ∞`, every order `k` and an
arbitrary open set `Ω`, every `u ∈ W^{k,p}(Ω)` is a limit, in the full Sobolev norm, of elements
whose values are represented by functions smooth on `Ω`. No boundedness or boundary regularity of
`Ω` is assumed. -/
theorem exists_contDiffOn_approximation (hp : p ≠ ⊤) (k : ℕ) (u : Wkp mu Omega p k) :
    ∃ (v : ℕ → Wkp mu Omega p k) (f : ℕ → E → ℝ),
      (∀ j, ContDiffOn ℝ ∞ (f j) Omega) ∧
      (∀ j, (value k (v j) : E → ℝ) =ᵐ[mu.restrict Omega] f j) ∧
      Tendsto v atTop (𝓝 u) := by
  choose v f hf hae hlt using fun j : ℕ =>
    exists_contDiffOn_norm_sub_lt hp k u (Nat.one_div_pos_of_nat (n := j))
  refine ⟨v, f, hf, hae, tendsto_iff_norm_sub_tendsto_zero.2 ?_⟩
  exact squeeze_zero (fun j => norm_nonneg _) (fun j => (hlt j).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- **Meyers–Serrin: `H = W` in `W^{k,p}(Ω)`.** For `1 ≤ p < ∞`, every order `k` and an
arbitrary open set `Ω`, the elements of `W^{k,p}(Ω)` represented by functions smooth on `Ω` are
dense in `W^{k,p}(Ω)`, in the full Sobolev norm. -/
theorem dense_contDiffOn_representatives (hp : p ≠ ⊤) (k : ℕ) :
    Dense {u : Wkp mu Omega p k | ∃ f : E → ℝ, ContDiffOn ℝ ∞ f Omega ∧
      (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f} := by
  intro u
  obtain ⟨v, f, hf, hae, hv⟩ := exists_contDiffOn_approximation hp k u
  exact mem_closure_of_tendsto hv (Eventually.of_forall fun j => ⟨f j, hf j, hae j⟩)

end TauCeti.Wkp
