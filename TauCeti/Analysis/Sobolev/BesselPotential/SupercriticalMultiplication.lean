/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.NormEquivalence.Basic
public import TauCeti.Analysis.Sobolev.Wkp.SupercriticalMultiplication
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Bilinear products in supercritical Bessel-potential spaces

Let `E` be a real inner product space of dimension `n` and let `n < p < ∞`, `1 < p`. For every
order `k ≥ 1` the Bessel-potential space `H^{k,p}(E)` is closed under pointwise products of
vector-valued functions: if `F` and `G` are finite-dimensional complex normed spaces, `K` is a
complex Banach space, `B : F →L[ℝ] G →L[ℝ] K` is real bilinear, and `u ∈ H^{k,p}(E, F)` and
`v ∈ H^{k,p}(E, G)` are `Lᵖ` functions, then `x ↦ B (u x) (v x)` is again an `Lᵖ` function in
`H^{k,p}(E, K)`
(`TemperedDistribution.MemSobolev.exists_memSobolev_bilin`). Only real bilinearity is asked of
`B`, so that quadratic expressions such as `B (u, conj u)` are included.

This is the form in which nonlinear terms enter elliptic regularity on the `Lᵖ` Sobolev scale:
once a solution lies in `H^{k,p}` with `p > n`, a quadratic nonlinearity `Q (u, u)` lies in the
same space, and an elliptic operator of order `m` returns the solution in `H^{k + m,p}`.

## The argument

The real-valued case is the algebra property of the weak-derivative spaces `W^{k,p}(E)`, `p > n`
(`TauCeti.Wkp.exists_value_ae_eq_mul`), transported through Calderón's identification of
`W^{k,p}(E)` with the real-valued elements of `H^{k,p}(E, ℂ)`
(`MeasureTheory.Lp.memSobolev_natCast_iff_exists_wkp_value_eq`). Vector values are reduced to real
values by real bases of `F` and `G`, since a real-linear functional of the values of an element
of `H^{k,p}` is the value of an element of `W^{k,p}`
(`TemperedDistribution.MemSobolev.exists_wkp_value_ae_eq_comp`), and conversely the value of an
element of `W^{k,p}` times a fixed vector is in `H^{k,p}`
(`TauCeti.Wkp.exists_memSobolev_value_smul`).

## References

* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Pure and Applied Mathematics 140,
  Academic Press, 2003, Theorem 4.39.
* A.-P. Calderón, *Lebesgue spaces of differentiable functions and distributions*, Proc. Sympos.
  Pure Math. **4** (1961), 33–49.
-/

public section

noncomputable section

open MeasureTheory Module TauCeti
open scoped ENNReal NNReal SchwartzMap BesselPotentialSpace

namespace TemperedDistribution

variable {E F G K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K]

section Product

variable {k : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [FiniteDimensional ℂ F] [FiniteDimensional ℂ G]

/-- **Bilinear products in supercritical Bessel-potential spaces.** Let `n < p` and `1 < p`,
where `n` is the dimension of `E`, and let `k ≥ 1`. Let `B` be a real bilinear map from
finite-dimensional complex normed spaces `F` and `G` to a complex Banach space `K`. For `Lᵖ`
functions `u ∈ H^{k,p}(E, F)` and `v ∈ H^{k,p}(E, G)`, the function `x ↦ B (u x) (v x)` is an
`Lᵖ` function in `H^{k,p}(E, K)`. -/
theorem MemSobolev.exists_memSobolev_bilin (hp : 1 < p) (hpn : (finrank ℝ E : ℝ≥0) < p)
    (hk : k ≠ 0) (B : F →L[ℝ] G →L[ℝ] K) {u : Lp F p (volume : Measure E)}
    {v : Lp G p (volume : Measure E)} (hu : MemSobolev k p (u : 𝓢'(E, F)))
    (hv : MemSobolev k p (v : 𝓢'(E, G))) :
    ∃ w : Lp K p (volume : Measure E), (w =ᵐ[volume] fun x ↦ B (u x) (v x)) ∧
      MemSobolev k p (w : 𝓢'(E, K)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  set bF := Module.finBasis ℝ F
  set bG := Module.finBasis ℝ G
  -- The real coordinates of `u` and `v` in the bases `bF` and `bG`, as elements of `W^{k,p}`.
  choose r hr using fun i ↦ hu.exists_wkp_value_ae_eq_comp (mod_cast hp) ENNReal.coe_ne_top
    (bF.coord i).toContinuousLinearMap
  choose t ht using fun j ↦ hv.exists_wkp_value_ae_eq_comp (mod_cast hp) ENNReal.coe_ne_top
    (bG.coord j).toContinuousLinearMap
  -- Their products, again in `W^{k,p}` since `p > n`.
  choose w hw using fun ij : _ × _ ↦
    Wkp.exists_value_ae_eq_mul hpn le_rfl le_rfl (r ij.1) (t ij.2)
  -- The products times the vectors `B (bF i) (bG j)`, as elements of `H^{k,p}(E, K)`.
  choose z hz hzS using fun ij : _ × _ ↦
    Wkp.exists_memSobolev_value_smul (mod_cast hp) ENNReal.coe_ne_top _ (w ij)
      (B (bF ij.1) (bG ij.2))
  have hsum : ∀ᵐ x ∂volume, ∑ ij, z ij x = B (u x) (v x) := by
    filter_upwards [ae_all_iff.2 hz, ae_all_iff.2 hw, ae_all_iff.2 hr, ae_all_iff.2 ht]
      with x hzx hwx hrx htx
    conv_rhs => rw [← bF.sum_repr (u x), ← bG.sum_repr (v x)]
    simp only [hzx, hwx, hrx, htx, map_sum, map_smul, sum_apply,
      smul_apply, Fintype.sum_prod_type, LinearMap.coe_toContinuousLinearMap',
      Basis.coord_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [smul_smul, mul_comm]
  refine ⟨∑ ij, z ij, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ z, hsum] with x h₁ h₂
    rw [h₁, h₂]
  rw [Lp.toTemperedDistribution_sum]
  exact MemSobolev.sum fun ij _ ↦ hzS ij

end Product

end TemperedDistribution
