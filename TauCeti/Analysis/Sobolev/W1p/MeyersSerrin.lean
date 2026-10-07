/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.CompactSupport

/-!
# Smooth functions are dense in `W^{1,p}(Ω)` (Meyers–Serrin)

For `1 ≤ p < ∞` and an **arbitrary** open set `Ω` of a finite-dimensional real inner product
space, the elements of `W^{1,p}(Ω)` with a representative which is smooth on `Ω` are dense in
`W^{1,p}(Ω)`, in the full Sobolev norm. In other words `H = W`: the closure of
`C^∞(Ω) ∩ W^{1,p}(Ω)` is all of `W^{1,p}(Ω)`. No boundedness and no regularity of the boundary
of `Ω` is assumed.

The approximants are smooth on `Ω` but need not be smooth up to its boundary, nor compactly
supported in `Ω`: on standard nontrivial bounded domains (for example, Euclidean balls in positive
dimension), `W^{1,p}_0(Ω)` is a proper subspace, so test functions are not dense. On the whole
space, density of globally smooth representatives at every order is
`TauCeti.Wkp.dense_contDiff_representatives`.

## The argument

Take a decomposition of unity `(ζ j)` of `Ω` by test functions, together with cutoffs `χ j` equal
to one on the support of `ζ j` and locally finite in `Ω`
(`IsOpen.exists_contDiff_decomposition_cutoff`). Each piece `ζ j u` is compactly supported in `Ω`,
so it lies in `W^{1,p}_0(Ω)` (`TauCeti.W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport`) and
is approximated by a test function `ψ j` to within `ε 2^{-j}`; cutting off, `χ j ψ j` still
approximates `ζ j u = χ j ζ j u`, and now has support where `χ j` does. The sum `f = ∑ j, χ j ψ j`
is locally finite in `Ω`, hence smooth there.

The series `∑ j, ζ j u` need not converge to `u` in `W^{1,p}(Ω)`: its partial sums are cutoffs
of `u`, and those converge to `u` only for `u ∈ W^{1,p}_0(Ω)`. So the comparison with `u` is made
through the corrections instead. These are absolutely summable in the Banach space `W^{1,p}(Ω)`,
to some `w` of norm at most `ε / 2`; after passing to a subsequence, representatives of their
partial sums converge almost everywhere on `Ω` to `f - u`. Hence `u + w` is within `ε` of `u`, and
its value is represented by `f`.

## Main declarations

* `TauCeti.W1p.exists_contDiffOn_approximation`: every `u ∈ W^{1,p}(Ω)` is a Sobolev-norm limit of
  elements with representatives smooth on `Ω`.
* `TauCeti.W1p.dense_contDiffOn_representatives`: those elements are dense in `W^{1,p}(Ω)`.

## References

* N. G. Meyers, J. Serrin, *H = W*, Proc. Nat. Acad. Sci. U.S.A. 51 (1964), 1055–1056.
* L. C. Evans, *Partial Differential Equations*, §5.3.2, Theorem 2.
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Gradient Topology

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- One piece of the gluing: if `χ = 1` on the support of `ζ`, then `ζ u` is approximated in
`W^{1,p}(Ω)`, to any accuracy, by a test function which vanishes wherever `χ` does. -/
private theorem W1p.exists_testFunction_norm_contDiffSMul_sub_le (hp : p ≠ ⊤) {zeta chi : E → ℝ}
    (hzeta : ContDiff ℝ ∞ zeta) (hzeta_cpt : HasCompactSupport zeta)
    (hzeta_ts : tsupport zeta ⊆ Omega) (hchi : ContDiff ℝ ∞ chi) (hchi_cpt : HasCompactSupport chi)
    (hchi_one : EqOn chi 1 (tsupport zeta)) {Mz : ℝ} (hMz0 : 0 ≤ Mz)
    (hMz : ∀ x ∈ Omega, |zeta x| ≤ Mz) (hMzg : ∀ x ∈ Omega, ‖∇ zeta x‖ ≤ Mz)
    (u : W1p mu Omega p) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Psi : 𝓓(Omega, ℝ), (∀ x, chi x = 0 → Psi x = 0) ∧
      ‖W1p.ofTestFunctionₗ mu Omega p Psi - W1p.contDiffSMul zeta hzeta hMz0 hMz hMzg u‖ ≤ δ := by
  obtain ⟨Mc, hMc0, hMc, hMcg⟩ := (hchi.of_le (by simp)).exists_abs_le_and_norm_gradient_le hchi_cpt
  set b := W1p.contDiffSMul zeta hzeta hMz0 hMz hMzg u
  let C := W1p.contDiffSMulL (mu := mu) (Omega := Omega) (p := p) chi hchi hMc0
    (fun x _ => hMc x) (fun x _ => hMcg x)
  -- approximate `b ∈ W^{1,p}_0(Ω)` by a test function `psi`, then cut off by `chi`
  have hb : b ∈ (w1p0Submodule mu Omega p : Set (W1p mu Omega p)) :=
    W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport hp hzeta hMz0 hMz hMzg hzeta_cpt
      hzeta_ts u
  rw [coe_w1p0Submodule, Metric.mem_closure_iff] at hb
  obtain ⟨_, ⟨psi, rfl⟩, hpsi⟩ := hb (δ / (2 * Mc + 1)) (by positivity)
  rw [dist_comm, dist_eq_norm] at hpsi
  let Psi : 𝓓(Omega, ℝ) :=
    ⟨chi * (psi : E → ℝ), hchi.mul psi.contDiff, psi.hasCompactSupport.mul_left,
      tsupport_mul_subset_right.trans psi.tsupport_subset⟩
  refine ⟨Psi, fun x hx => by simp [Psi, hx], ?_⟩
  have ha : W1p.ofTestFunctionₗ mu Omega p Psi = C (W1p.ofTestFunctionₗ mu Omega p psi) := by
    rw [W1p.contDiffSMulL_apply, W1p.contDiffSMul_ofTestFunctionₗ _ _ _ _ psi Psi rfl]
  -- `chi = 1` on the support of `zeta`, so the cutoff fixes `b`
  have hbC : b = C b := by
    refine W1p.ext_value (Lp.ext ?_)
    rw [W1p.contDiffSMulL_apply]
    filter_upwards [W1p.value_contDiffSMul_ae hzeta hMz0 hMz hMzg u,
      W1p.value_contDiffSMul_ae hchi hMc0 (fun x _ => hMc x) (fun x _ => hMcg x) b]
      with x hx hCx
    rw [hCx, hx, smul_eq_mul, smul_eq_mul]
    by_cases hxz : x ∈ tsupport zeta
    · rw [hchi_one hxz, Pi.one_apply, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hxz, zero_mul, mul_zero]
  rw [ha, hbC, ← map_sub]
  calc ‖C (W1p.ofTestFunctionₗ mu Omega p psi - b)‖
      ≤ 2 * Mc * ‖W1p.ofTestFunctionₗ mu Omega p psi - b‖ := by
        rw [W1p.contDiffSMulL_apply]
        exact W1p.norm_contDiffSMul_le _ _ _ _ _
    _ ≤ (2 * Mc + 1) * (δ / (2 * Mc + 1)) := by
        gcongr
        linarith
    _ = δ := by field_simp

/-- Every `u ∈ W^{1,p}(Ω)`, `p < ∞`, is within `ε` of an element whose value is represented by a
function smooth on `Ω`. -/
private theorem W1p.exists_contDiffOn_norm_sub_lt (hp : p ≠ ⊤) (u : W1p mu Omega p) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (v : W1p mu Omega p) (f : E → ℝ), ContDiffOn ℝ ∞ f Omega ∧
      (W1p.value v : E → ℝ) =ᵐ[mu.restrict Omega] f ∧ ‖v - u‖ < ε := by
  obtain ⟨zeta, chi, hzeta, hchi, hchi_one, hfin⟩ :=
    IsOpen.exists_contDiff_decomposition_cutoff Omega.isOpen
  choose Mz hMz0 hMz hMzg using fun j =>
    ((hzeta j).1.of_le (by simp)).exists_abs_le_and_norm_gradient_le (hzeta j).2.1
  -- the localized pieces `b j = ζ_j u`, and test functions `a j` within `ε 2^{-j-2}` of them,
  -- supported where the locally finite cutoffs `χ_j` are
  let b : ℕ → W1p mu Omega p := fun j =>
    W1p.contDiffSMul (zeta j) (hzeta j).1 (hMz0 j) (fun x _ => hMz j x) (fun x _ => hMzg j x) u
  choose Psi hPsi_zero hab using fun j =>
    W1p.exists_testFunction_norm_contDiffSMul_sub_le hp (hzeta j).1 (hzeta j).2.1 (hzeta j).2.2
      (hchi j).1 (hchi j).2.1 (hchi_one j) (hMz0 j) (fun x _ => hMz j x) (fun x _ => hMzg j x)
      u (δ := ε / 4 * (1 / 2) ^ j) (by positivity)
  let a : ℕ → W1p mu Omega p := fun j => W1p.ofTestFunctionₗ mu Omega p (Psi j)
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
  let S : ℕ → W1p mu Omega p := fun N => ∑ j ∈ Finset.range N, (a j - b j)
  have hSv : Tendsto (fun N => W1p.value (S N)) atTop (𝓝 (W1p.value w)) := by
    have h := ((W1p.valueL (mu := mu) (Omega := Omega) (p := p)).continuous.tendsto w).comp
      hsummable.hasSum.tendsto_sum_nat
    simpa only [Function.comp_def, W1p.valueL_apply] using h
  obtain ⟨ns, hns, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hSv).exists_seq_tendsto_ae
  have hterm : ∀ᵐ x ∂mu.restrict Omega, ∀ j,
      W1p.value (a j - b j) x = Psi j x - zeta j x * W1p.value u x := by
    rw [ae_all_iff]
    intro j
    rw [← W1p.valueL_apply, map_sub, W1p.valueL_apply, W1p.valueL_apply]
    filter_upwards [Lp.coeFn_sub (W1p.value (a j)) (W1p.value (b j)),
      testFunctionLp_apply_ae (mu := mu) p (Psi j),
      W1p.value_contDiffSMul_ae (hzeta j).1 (hMz0 j) (fun x _ => hMz j x)
        (fun x _ => hMzg j x) u] with x hsub ha hb
    rw [hsub, Pi.sub_apply, hb, smul_eq_mul, ← ha, W1p.value_ofTestFunctionₗ]
  have hpartial : ∀ᵐ x ∂mu.restrict Omega, ∀ N,
      W1p.value (S N) x = ∑ j ∈ Finset.range N, (Psi j x - zeta j x * W1p.value u x) := by
    rw [ae_all_iff]
    intro N
    filter_upwards [W1p.value_finsetSum_ae (Finset.range N) fun j => a j - b j, hterm]
      with x hx hterm
    rw [hx]
    exact Finset.sum_congr rfl fun j _ => hterm j
  have hw_ae : ∀ᵐ x ∂mu.restrict Omega, W1p.value w x = f x - W1p.value u x := by
    filter_upwards [hlim, hpartial, ae_restrict_mem Omega.isOpen.measurableSet]
      with x hx hpx hxΩ
    obtain ⟨m, hm⟩ := hf_local x hxΩ
    have hconv : Tendsto (fun N => W1p.value (S N) x) atTop (𝓝 (f x - W1p.value u x)) := by
      refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨m, fun N hN => Eq.symm ?_⟩)
      beta_reduce
      obtain ⟨hf_eq, hz_eq⟩ := hm N hN
      rw [hpx, Finset.sum_sub_distrib, ← Finset.sum_mul, hf_eq, hz_eq, one_mul]
    exact tendsto_nhds_unique hx (hconv.comp hns.tendsto_atTop)
  refine ⟨u + w, f, hf, ?_, ?_⟩
  · have hadd : W1p.value (u + w) = W1p.value u + W1p.value w := by
      simp only [← W1p.valueL_apply, map_add]
    filter_upwards [Lp.coeFn_add (W1p.value u) (W1p.value w), hw_ae] with x hx hwx
    rw [hadd, hx, Pi.add_apply, hwx, add_sub_cancel]
  · rw [add_sub_cancel_left]
    linarith

/-- **Meyers–Serrin approximation in `W^{1,p}(Ω)`.** For `1 ≤ p < ∞` and an arbitrary open set
`Ω`, every `u ∈ W^{1,p}(Ω)` is a limit, in the full Sobolev norm, of elements whose values are
represented by functions smooth on `Ω`. No boundedness or boundary regularity of `Ω` is
assumed. -/
theorem W1p.exists_contDiffOn_approximation (hp : p ≠ ⊤) (u : W1p mu Omega p) :
    ∃ (v : ℕ → W1p mu Omega p) (f : ℕ → E → ℝ),
      (∀ j, ContDiffOn ℝ ∞ (f j) Omega) ∧
      (∀ j, (W1p.value (v j) : E → ℝ) =ᵐ[mu.restrict Omega] f j) ∧
      Tendsto v atTop (𝓝 u) := by
  choose v f hf hae hlt using fun j : ℕ =>
    W1p.exists_contDiffOn_norm_sub_lt hp u (Nat.one_div_pos_of_nat (n := j))
  refine ⟨v, f, hf, hae, tendsto_iff_norm_sub_tendsto_zero.2 ?_⟩
  exact squeeze_zero (fun j => norm_nonneg _) (fun j => (hlt j).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- **Meyers–Serrin: `H = W` in `W^{1,p}(Ω)`.** For `1 ≤ p < ∞` and an arbitrary open set `Ω`,
the elements of `W^{1,p}(Ω)` represented by functions smooth on `Ω` are dense in `W^{1,p}(Ω)`,
in the full Sobolev norm. -/
theorem W1p.dense_contDiffOn_representatives (hp : p ≠ ⊤) :
    Dense {u : W1p mu Omega p | ∃ f : E → ℝ, ContDiffOn ℝ ∞ f Omega ∧
      (W1p.value u : E → ℝ) =ᵐ[mu.restrict Omega] f} := by
  intro u
  obtain ⟨v, f, hf, hae, hv⟩ := W1p.exists_contDiffOn_approximation hp u
  exact mem_closure_of_tendsto hv (Eventually.of_forall fun j => ⟨f j, hf j, hae j⟩)

end TauCeti
