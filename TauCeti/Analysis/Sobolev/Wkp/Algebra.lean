/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
public import TauCeti.Analysis.Sobolev.BesselPotential.NormEquivalence.Basic
public import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# `W^{k,2}(ℝⁿ)`, `2k > n`, is an algebra

Let `E` be a finite-dimensional real inner product space of dimension `n` and let `2k > n`. The
weak-derivative Sobolev space `W^{k,2}(E)` on the whole space is closed under pointwise
multiplication, with the estimate

`‖u v‖_{W^{k,2}} ≤ C ‖u‖_{W^{k,2}} ‖v‖_{W^{k,2}}`

for a constant `C` depending only on `E` and `k` (`TauCeti.Wkp.exists_norm_mul_le`). This is the
algebra property of the Bessel-potential space `H^k(E)` (`BesselPotentialSpace.mulCLM`),
transported through the bounded embedding `TauCeti.Wkp.toBesselPotentialSpace` of `W^{k,2}(E)`
into `H^{k,2}(E, ℂ)`, whose range is the real-valued elements and whose inverse is bounded on
that range.

For classical functions this gives the estimate that, together with the sup bound
`sup_x |f(x)| ≤ C ∑_{i ≤ k} ‖Dⁱ f‖₂` (`TauCeti.exists_norm_le_mul_sum_lpNorm_iteratedFDeriv`),
makes the `L²` norms of the derivatives through order `k` behave like a Banach algebra norm. If
`f` and `g` are `Cᵏ` on `E` and their derivatives through order `k` are square integrable, then
the derivatives of `f g` through order `k` are square integrable, and
`∑_{i ≤ k} ‖Dⁱ (f g)‖₂ ≤ C (∑_{i ≤ k} ‖Dⁱ f‖₂) (∑_{i ≤ k} ‖Dⁱ g‖₂)`
(`TauCeti.exists_sum_lpNorm_iteratedFDeriv_mul_le`).

These are the estimates behind nonlinear analysis on the scale of `L²` derivatives of order
`k > n / 2`: polynomial expressions of such functions stay in the scale, with norms controlled by
those of their factors. No explicit value of the constants is claimed.

## References

* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Pure and Applied Mathematics 140,
  Academic Press, 2003, Theorem 4.39.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace TemperedDistribution BesselPotentialSpace Module
open scoped ENNReal BesselPotentialSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {k : ℕ}

namespace Wkp

/-- The product in `H^k(E)` of the images of `u, v ∈ W^{k,2}(E)` is the image of an element of
`W^{k,2}(E)` whose value is the pointwise product of the values of `u` and `v`. -/
private theorem exists_toBesselPotentialSpace_eq_mulCLM (hk : finrank ℝ E < 2 * k)
    (u v : Wkp (volume : Measure E) ⊤ 2 k) :
    ∃ w : Wkp (volume : Measure E) ⊤ 2 k,
      toBesselPotentialSpace ENNReal.one_lt_two ENNReal.ofNat_ne_top k w =
        mulCLM (by exact_mod_cast hk)
          (toBesselPotentialSpace ENNReal.one_lt_two ENNReal.ofNat_ne_top k u)
          (toBesselPotentialSpace ENNReal.one_lt_two ENNReal.ofNat_ne_top k v) ∧
      (value k w : E → ℝ) =ᵐ[volume] (fun x ↦ value k u x * value k v x) := by
  have hs : (finrank ℝ E : ℝ) < 2 * (k : ℝ) := by exact_mod_cast hk
  have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hres : (volume : Measure E).restrict ((⊤ : Opens E) : Set E) = volume :=
    Measure.restrict_coe_opens_top volume
  set T := toBesselPotentialSpace (E := E) ENNReal.one_lt_two ENNReal.ofNat_ne_top k
  -- The product of the values is square integrable, since the value of `u` is bounded.
  have hvL : MemLp (value k v : E → ℝ) 2 volume := by
    simpa only [hres] using Lp.memLp (value k v)
  have hm : MemLp (fun x ↦ value k u x * value k v x) 2 volume := by
    refine ((toZeroAtInfty hk u).toBCF.memLp_top (μ := volume)).mul hvL |>.ae_eq ?_
    filter_upwards [value_ae_eq_toZeroAtInfty hk u] with x hx
    simp [hx]
  set g := hm.toLp _
  -- The product of `T u` and `T v` in `H^k` is the complexification of the product of values.
  set P := mulCLM hs (T u) (T v)
  have hP : BesselPotentialSpace.inclusionLp h0 P = Complex.ofRealCLM.compLp g := by
    refine Lp.ext ?_
    rw [← toLp_inclusion]
    filter_upwards [coeFn_toLp_inclusion_mulCLM hs h0 (T u) (T v),
      coeFn_inclusionLp_toBesselPotentialSpace ENNReal.one_lt_two ENNReal.ofNat_ne_top k u,
      coeFn_inclusionLp_toBesselPotentialSpace ENNReal.one_lt_two ENNReal.ofNat_ne_top k v,
      Complex.ofRealCLM.coeFn_compLp (p := 2) (μ := volume) g, hm.coeFn_toLp] with
      x hx hu hv hgx hg
    rw [hx, toLp_inclusion, toLp_inclusion, hu, hv, hgx, hg, Complex.ofRealCLM_apply,
      Complex.ofReal_mul]
  -- So `P` lies in the range of `T`, and its preimage has the product as its value.
  obtain ⟨w, hw⟩ := (exists_toBesselPotentialSpace_eq_iff ENNReal.one_lt_two
    ENNReal.ofNat_ne_top k P).2 ⟨g, ((BesselPotentialSpace.inclusionLp_eq_iff h0).1 hP).symm⟩
  refine ⟨w, hw, ?_⟩
  have hwP := (toBesselPotentialSpace_eq_iff ENNReal.one_lt_two ENNReal.ofNat_ne_top).1 hw
  rw [hP] at hwP
  filter_upwards [hwP, Complex.ofRealCLM.coeFn_compLp (p := 2) (μ := volume) g,
    hm.coeFn_toLp] with x hx hgx hg
  rw [hgx, hg, Complex.ofRealCLM_apply] at hx
  exact_mod_cast hx.symm

/-- **`W^{k,2}(E)`, `2k > dim E`, is an algebra.** There is a constant `C` such that for all
`u, v ∈ W^{k,2}(E)` on the whole space, the pointwise product of their values is the value of some
`w ∈ W^{k,2}(E)` with `‖w‖ ≤ C ‖u‖ ‖v‖`. -/
theorem exists_norm_mul_le (hk : finrank ℝ E < 2 * k) :
    ∃ C, ∀ u v : Wkp (volume : Measure E) ⊤ 2 k, ∃ w : Wkp (volume : Measure E) ⊤ 2 k,
      (value k w : E → ℝ) =ᵐ[volume] (fun x ↦ value k u x * value k v x) ∧
        ‖w‖ ≤ C * ‖u‖ * ‖v‖ := by
  have hs : (finrank ℝ E : ℝ) < 2 * (k : ℝ) := by exact_mod_cast hk
  set T := toBesselPotentialSpace (E := E) ENNReal.one_lt_two ENNReal.ofNat_ne_top k
  obtain ⟨C₁, hC₁⟩ := exists_norm_le_mul_norm_toBesselPotentialSpace (E := E)
    ENNReal.one_lt_two ENNReal.ofNat_ne_top k
  set M := mulCLM (E := E) hs
  refine ⟨max C₁ 0 * (‖M‖ * ‖T‖ * ‖T‖), fun u v ↦ ?_⟩
  obtain ⟨w, hw, hwv⟩ := exists_toBesselPotentialSpace_eq_mulCLM hk u v
  refine ⟨w, hwv, ?_⟩
  -- `‖w‖ ≤ C₁ ‖T w‖` and `T w = M (T u) (T v)`.
  have hTw : ‖w‖ ≤ max C₁ 0 * ‖M (T u) (T v)‖ := by
    rw [← hw]
    exact (hC₁ w).trans (by gcongr; exact le_max_left _ _)
  have hPle : ‖M (T u) (T v)‖ ≤ ‖M‖ * ‖T‖ * ‖T‖ * (‖u‖ * ‖v‖) := by
    calc ‖M (T u) (T v)‖ ≤ ‖M‖ * ‖T u‖ * ‖T v‖ := M.le_opNorm₂ (T u) (T v)
      _ ≤ ‖M‖ * (‖T‖ * ‖u‖) * (‖T‖ * ‖v‖) := by
        gcongr
        · exact T.le_opNorm u
        · exact T.le_opNorm v
      _ = ‖M‖ * ‖T‖ * ‖T‖ * (‖u‖ * ‖v‖) := by ring
  calc ‖w‖ ≤ max C₁ 0 * (‖M‖ * ‖T‖ * ‖T‖ * (‖u‖ * ‖v‖)) :=
        hTw.trans (mul_le_mul_of_nonneg_left hPle (le_max_right _ _))
    _ = max C₁ 0 * (‖M‖ * ‖T‖ * ‖T‖) * ‖u‖ * ‖v‖ := by ring

end Wkp

/-- **Products of classical functions with square-integrable derivatives.** If `2k > dim E`, there
is a constant `C` such that for all functions `f` and `g` that are `Cᵏ` on `E` with
square-integrable derivatives through order `k`, the derivatives of `f g` through order `k` are
square integrable and

`∑_{i ≤ k} ‖Dⁱ (f g)‖₂ ≤ C (∑_{i ≤ k} ‖Dⁱ f‖₂) (∑_{i ≤ k} ‖Dⁱ g‖₂)`. -/
theorem exists_sum_lpNorm_iteratedFDeriv_mul_le (hk : finrank ℝ E < 2 * k) :
    ∃ C, ∀ f g : E → ℝ, ContDiff ℝ k f → ContDiff ℝ k g →
      (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) 2) → (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i g) 2) →
      (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i (f * g)) 2) ∧
        ∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i (f * g)) 2 volume ≤
          C * (∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i f) 2 volume) *
            ∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i g) 2 volume := by
  have hres : (volume : Measure E).restrict ((⊤ : Opens E) : Set E) = volume :=
    Measure.restrict_coe_opens_top volume
  obtain ⟨C, hC⟩ := Wkp.exists_norm_mul_le (E := E) hk
  refine ⟨(k + 1) * max C 0, fun f g hf hg hfm hgm ↦ ?_⟩
  obtain ⟨u, hu, hun⟩ := Wkp.exists_value_ae_eq_and_norm_le hf hfm
  obtain ⟨v, hv, hvn⟩ := Wkp.exists_value_ae_eq_and_norm_le hg hgm
  obtain ⟨w, hw, hwn⟩ := hC u v
  have hfg : ContDiff ℝ k (f * g) := hf.mul hg
  -- `w` represents `f g`.
  have hw' : (Wkp.value k w : E → ℝ) =ᵐ[(volume : Measure E).restrict ((⊤ : Opens E) : Set E)]
      f * g := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hw, hu, hv] with x hx hux hvx
    rw [hx, hux, hvx, Pi.mul_apply]
  refine ⟨fun i hi ↦ by
    simpa only [hres] using Wkp.memLp_iteratedFDeriv_of_contDiffOn k w hfg.contDiffOn hw' i hi, ?_⟩
  have hle : ∀ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i (f * g)) 2 volume ≤ ‖w‖ :=
    fun i hi ↦ by
      simpa only [hres] using Wkp.lpNorm_iteratedFDeriv_le_of_contDiffOn k w hfg.contDiffOn hw' i
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  have hSf : 0 ≤ ∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i f) 2 volume :=
    (norm_nonneg u).trans hun
  have hwC : ‖w‖ ≤ max C 0 *
      (∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i f) 2 volume) *
        ∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i g) 2 volume :=
    hwn.trans <| mul_le_mul (mul_le_mul (le_max_left _ _) hun (norm_nonneg _) (le_max_right _ _))
      hvn (norm_nonneg _) (mul_nonneg (le_max_right _ _) hSf)
  calc ∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i (f * g)) 2 volume
      ≤ ∑ _i ∈ Finset.range (k + 1), ‖w‖ := Finset.sum_le_sum hle
    _ = (k + 1) * ‖w‖ := by simp
    _ ≤ (k + 1) * (max C 0 *
          (∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i f) 2 volume) *
            ∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i g) 2 volume) := by
      gcongr
    _ = (k + 1) * max C 0 *
          (∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i f) 2 volume) *
            ∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i g) 2 volume := by ring

end TauCeti
