/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.CoefficientCompactness
public import TauCeti.Analysis.Complex.Wirtinger.Regularity.Holder
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Analysis.Polynomial.Monic.RootBound
import TauCeti.Analysis.Polynomial.ContinuityOfRoots.Holder
import TauCeti.RingTheory.Polynomial.Vieta
import TauCeti.Topology.MetricSpace.Holder

/-!
# Regularity of Hölder solutions of the equation of elementary symmetric functions

Let `D = \bar∂ + ν W + μ \bar W` be a real Cauchy–Riemann operator on functions of `z ∈ ℂ`, with
`(0,1)`-form coefficients `ν` and `μ`. If `R(z)` is a multiset of `m` solutions of `D`, the
elementary symmetric functions `c_j = e_j(R)`, `1 ≤ j ≤ m`, the signed coefficients of
`∏_{w ∈ R} (W - w)`, solve

`\bar∂ c_j + j ν c_j + μ ∑_{w ∈ R} \bar w e_{j-1}(R ∖ w) = 0`.

Limits of approximate solutions of this equation are a priori only Hölder continuous, of some
exponent `α`, and solve it in the sense of distributions
(`TauCeti.exists_strictMono_hasWeakConjWirtingerDerivOn_of_esymm`). This file proves that such
solutions are `C¹` and solve the equation classically, which is the form in which the root
branches of `TauCeti.Analysis.Complex.Wirtinger.Root.Branch` and their normalization across
collisions in `TauCeti.Analysis.Complex.Wirtinger.Root.Normalization` consume it.

The zeroth-order term `j ν c_j + μ ∑_{w ∈ R} \bar w e_{j-1}(R ∖ w)` is not a polynomial in the
coefficients `c_i`: the sum `∑_{w ∈ R} \bar w e_{j-1}(R ∖ w)` involves the roots and their
conjugates. By Ostrowski's theorem (`Multiset.rel_norm_sub_le_of_norm_esymm_sub_le`) the roots
of polynomials with bounded `α`-Hölder coefficients match, with multiplicity, within a constant
times `|z - z'|^(α / m)`. Replacing one root `a` of a multiset `u` by `b` changes the sum by
`(\bar a - \bar b) e_{j-1}(u) + (a - b) ∑_{w ∈ u} \bar w e_{j-2}(u ∖ w)`
(`Multiset.sum_map_mul_esymm_erase_cons`), at most a constant times `|a - b|` for bounded roots,
so the sum is Hölder of exponent `α / m` on compact sets
(`TauCeti.exists_holderOnWith_sum_map_conj_mul_esymm_erase`). With `ν` and `μ` Hölder of the
same exponent, the right side of `\bar∂ c_j = -(j ν c_j + μ ∑ \bar w e_{j-1}(R ∖ w))` is locally
Hölder, and the interior Schauder estimate for `\bar∂`
(`TauCeti.HasWeakConjWirtingerDerivOn.contDiffOn_one_of_holderOnWith`) makes `c_j` a `C¹`
classical solution with locally `(α / m)`-Hölder derivative
(`TauCeti.contDiffOn_and_conjWirtingerDeriv_add_add_eq_zero_of_esymm`). Applied to the limits of
`TauCeti.exists_strictMono_hasWeakConjWirtingerDerivOn_of_esymm`, when the limit forms `ν₀` and
`μ₀` are `((1 - 2 / p) / m)`-Hölder on compact sets, this gives `C¹` limits solving the equation
classically (`TauCeti.exists_strictMono_contDiffOn_of_esymm`).

## Main results

* `TauCeti.exists_holderOnWith_sum_map_conj_mul_esymm_erase`: if the elementary symmetric
  functions of multisets `R z` of `m` complex numbers are bounded and `α`-Hölder on a set, then
  `∑_{w ∈ R z} \bar w e_k(R z ∖ w)` is `(α / m)`-Hölder there.
* `TauCeti.contDiffOn_and_conjWirtingerDeriv_add_add_eq_zero_of_esymm`: locally `α`-Hölder weak
  solutions of the equation of elementary symmetric functions, with locally `(α / m)`-Hölder
  coefficients `ν` and `μ`, are `C¹` classical solutions.
* `TauCeti.exists_strictMono_contDiffOn_of_esymm`: subsequential limits of approximate solutions
  are `C¹` classical solutions when the limit forms are Hölder on compact sets.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 6.
* A. M. Ostrowski, *Solution of Equations in Euclidean and Banach Spaces*, Academic Press, 1973,
  Appendix A.
-/

public section

open scoped NNReal ComplexConjugate Topology ContDiff
open MeasureTheory Set Filter Metric

namespace TauCeti

/-! ### The zeroth-order term is Hölder in the coefficients -/

/-- Replacing one element `a` of `a :: u` by `b` changes `∑_{w ∈ a :: u} \bar w e_k((a :: u) ∖ w)`
by at most `(C(m, k) Mᵏ + m M C(m, k - 1) M^(k-1)) ‖a - b‖`, when `u` has at most `m` elements
and all elements have norm at most `M`. -/
private theorem norm_sum_map_conj_mul_esymm_erase_cons_sub_le {m k : ℕ} {M : ℝ} (hM : 0 ≤ M)
    {a b : ℂ} {u : Multiset ℂ} (hu : ∀ w ∈ u, ‖w‖ ≤ M) (hum : Multiset.card u ≤ m) :
    ‖((a ::ₘ u).map fun w ↦ conj w * ((a ::ₘ u).erase w).esymm k).sum -
      ((b ::ₘ u).map fun w ↦ conj w * ((b ::ₘ u).erase w).esymm k).sum‖ ≤
        (m.choose k * M ^ k + m * M * (m.choose (k - 1) * M ^ (k - 1))) * ‖a - b‖ := by
  cases k with
  | zero =>
    -- `e₀ = 1`, so the sums are `∑ \bar w` and differ by `\bar a - \bar b`
    simp only [Multiset.esymm_zero, mul_one, Multiset.map_cons, Multiset.sum_cons,
      add_sub_add_right_eq_sub, ← map_sub, Complex.norm_conj, Nat.choose_zero_right,
      Nat.cast_one, pow_zero]
    exact le_mul_of_one_le_left (norm_nonneg _) (le_add_of_nonneg_right (by positivity))
  | succ k =>
    rw [Multiset.sum_map_mul_esymm_erase_cons, Multiset.sum_map_mul_esymm_erase_cons,
      Nat.add_sub_cancel]
    have he : ‖u.esymm (k + 1)‖ ≤ m.choose (k + 1) * M ^ (k + 1) :=
      (Multiset.norm_esymm_le hu _).trans (by gcongr)
    have hS := norm_sum_map_conj_mul_esymm_erase_le (k := k) hM hum hu
    calc _ = ‖conj (a - b) * u.esymm (k + 1) +
          (a - b) * (u.map fun w ↦ conj w * (u.erase w).esymm k).sum‖ := by
          rw [map_sub]
          ring_nf
      _ ≤ ‖a - b‖ * (m.choose (k + 1) * M ^ (k + 1)) +
          ‖a - b‖ * (m * M * (m.choose k * M ^ k)) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul, Complex.norm_conj]
            gcongr
          · rw [norm_mul]
            gcongr
      _ = _ := by ring

/-- **The zeroth-order term of the equation is Hölder in the coefficients.** Let `R z` be a
multiset of `m` complex numbers for `z ∈ K`, whose elementary symmetric functions `e_j(R z)`,
`1 ≤ j ≤ m`, have norm at most `B` and are `α`-Hölder on `K` with constant `C`. Then for every `k`,
`z ↦ ∑_{w ∈ R z} \bar w e_k(R z ∖ w)` is `(α / m)`-Hölder on `K`. -/
theorem exists_holderOnWith_sum_map_conj_mul_esymm_erase {m : ℕ} (k : ℕ) {K : Set ℂ}
    {R : ℂ → Multiset ℂ} {B C α : ℝ≥0} (hcard : ∀ z ∈ K, Multiset.card (R z) = m)
    (hB : ∀ j ∈ Finset.Icc 1 m, ∀ z ∈ K, ‖(R z).esymm j‖ ≤ B)
    (hC : ∀ j ∈ Finset.Icc 1 m, HolderOnWith C α (fun z ↦ (R z).esymm j) K) :
    ∃ C' : ℝ≥0, HolderOnWith C' (α / m)
      (fun z ↦ ((R z).map fun w ↦ conj w * ((R z).erase w).esymm k).sum) K := by
  -- for `m = 0` the multisets are empty and the term vanishes
  rcases eq_or_ne m 0 with rfl | hm
  · refine ⟨0, HolderOnWith.of_dist_le fun z hz y hy ↦ ?_⟩
    simp [Multiset.card_eq_zero.1 (hcard z hz), Multiset.card_eq_zero.1 (hcard y hy)]
  set M : ℝ := B + 1
  have hM : 0 ≤ M := by positivity
  -- the roots are bounded, by Cauchy's bound
  have hroot (z : ℂ) (hz : z ∈ K) : ∀ w ∈ R z, ‖w‖ ≤ M := fun w hw ↦
    (Multiset.norm_lt_add_one_of_norm_esymm_le (fun j hj ↦ hB j (hcard z hz ▸ hj) z hz) hw).le
  -- replacing one root changes the zeroth-order term by a multiple `L` of the displacement
  set L : ℝ := m.choose k * M ^ k + m * M * (m.choose (k - 1) * M ^ (k - 1))
  have hL : 0 ≤ L := by positivity
  set A : ℝ := (2 * m - 1) * (m * C * (B + 1) ^ (m - 1)) ^ ((m : ℝ)⁻¹)
  refine ⟨(m * (L * A)).toNNReal, HolderOnWith.of_dist_le fun z hz y hy ↦ ?_⟩
  have hδ : ∀ j ∈ Finset.Icc 1 (Multiset.card (R z)),
      ‖(R y).esymm j - (R z).esymm j‖ ≤ C * dist z y ^ (α : ℝ) := fun j hj ↦ by
    rw [← dist_eq_norm, dist_comm]
    exact (hC j (hcard z hz ▸ hj)).dist_le hz hy
  -- by Ostrowski's theorem the roots match within `A |z - y|^(α / m)`
  have hrel := Multiset.rel_norm_sub_le_of_norm_esymm_sub_le ((hcard y hy).trans (hcard z hz).symm)
    (fun j hj ↦ hB j (hcard z hz ▸ hj) z hz) (fun j hj ↦ hB j (hcard z hz ▸ hj) y hy) hδ
  have hA : (2 * (Multiset.card (R z) : ℝ) - 1) * (Multiset.card (R z) * (C * dist z y ^ (α : ℝ)) *
      ((B : ℝ) + 1) ^ (Multiset.card (R z) - 1)) ^ ((Multiset.card (R z) : ℝ)⁻¹) =
        A * dist z y ^ ((α / m : ℝ≥0) : ℝ) := by
    rw [hcard z hz, NNReal.coe_div, NNReal.coe_natCast, div_eq_mul_inv, Real.rpow_mul dist_nonneg,
      show (m : ℝ) * (C * dist z y ^ (α : ℝ)) * ((B : ℝ) + 1) ^ (m - 1) =
        m * C * ((B : ℝ) + 1) ^ (m - 1) * dist z y ^ (α : ℝ) by ring,
      Real.mul_rpow (by positivity) (by positivity)]
    simp only [A]
    ring
  rw [hA] at hrel
  have h := hrel.norm_sub_le_of_norm_sub_le_cons
    (Φ := fun s ↦ (s.map fun w ↦ conj w * (s.erase w).esymm k).sum) hL
    (fun a b u _ _ hu hun ↦ norm_sum_map_conj_mul_esymm_erase_cons_sub_le hM hu hun.le)
    (hroot z hz) (hroot y hy) (hcard z hz).le
  have hA0 : 0 ≤ A := mul_nonneg (by
    have : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hm
    linarith) (by positivity)
  rw [dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
  refine h.trans (le_of_eq ?_)
  rw [hcard z hz]
  ring

/-! ### The equation of elementary symmetric functions -/

/-- The right side `-(j ν c_j + μ ∑_{w ∈ R} \bar w e_{j-1}(R ∖ w))(1)` of the equation of
elementary symmetric functions is `(α / m)`-Hölder on a compact set `K` on which the coefficients
`c_i = e_i(R)` are `α`-Hölder and the forms `ν` and `μ` are `(α / m)`-Hölder. -/
private theorem exists_holderOnWith_neg_smul_add_smul_apply_one {m j : ℕ}
    (hj : j ∈ Finset.Icc 1 m) {α : ℝ≥0} {K : Set ℂ} (hK : IsCompact K) {c : ℕ → ℂ → ℂ}
    {R : ℂ → Multiset ℂ} {ν μ : ℂ → ℂ →L⋆[ℂ] ℂ}
    (hR : ∀ z ∈ K, Multiset.card (R z) = m ∧ ∀ i ∈ Finset.Icc 1 m, c i z = (R z).esymm i)
    (hc : ∀ i ∈ Finset.Icc 1 m, ∃ C, HolderOnWith C α (c i) K)
    (hν : ∃ C, HolderOnWith C (α / m) ν K) (hμ : ∃ C, HolderOnWith C (α / m) μ K) :
    ∃ C, HolderOnWith C (α / m) (fun z ↦ -((j * c j z) • ν z +
      ((R z).map fun w ↦ conj w * ((R z).erase w).esymm (j - 1)).sum • μ z) 1) K := by
  have hm : m ≠ 0 := by have := Finset.mem_Icc.1 hj; omega
  have hβα : α / m ≤ α := div_le_self zero_le (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hm)
  -- functions Hölder on the compact set `K` are bounded there
  have hbd {f : ℂ → ℂ} {C r : ℝ≥0} (hf : HolderOnWith C r f K) :
      ∃ D : ℝ≥0, ∀ z ∈ K, ‖f z‖ ≤ D := by
    obtain ⟨D, hD⟩ := isBounded_iff_forall_norm_le.1 (hf.isBounded_image hK.isBounded)
    exact ⟨D.toNNReal, fun z hz ↦ (hD _ (mem_image_of_mem f hz)).trans (Real.le_coe_toNNReal D)⟩
  -- the coefficients, bounded and `α`-Hölder on `K`, hence `(α / m)`-Hölder
  choose! Cc hCc using hc
  choose! Dc hDc using fun i hi ↦ hbd (hCc i hi)
  have hjc := ((hCc j hj).of_le_of_norm_le (hDc j hj) hβα one_pos).smul (j : ℂ)
  -- the zeroth-order term, through the roots
  obtain ⟨CS, hCS⟩ := exists_holderOnWith_sum_map_conj_mul_esymm_erase (j - 1)
    (R := R) (B := ∑ i ∈ Finset.Icc 1 m, Dc i) (C := ∑ i ∈ Finset.Icc 1 m, Cc i)
    (fun z hz ↦ (hR z hz).1)
    (fun i hi z hz ↦ (hR z hz).2 i hi ▸ (hDc i hi z hz).trans
      (by exact_mod_cast Finset.single_le_sum (f := Dc) (fun i _ ↦ zero_le) hi))
    (fun i hi ↦ ((hCc i hi).mono_const (Finset.single_le_sum (f := Cc) (fun i _ ↦ zero_le)
      hi)).congr fun z hz ↦ (hR z hz).2 i hi)
  obtain ⟨DS, hDS⟩ := hbd hCS
  -- the forms evaluated at `1`
  have hev := ContinuousLinearMap.lipschitzWith_apply (σ₁₂ := starRingEnd ℂ) (F := ℂ) (1 : ℂ)
  obtain ⟨Cν, hCν⟩ := hν
  obtain ⟨Cμ, hCμ⟩ := hμ
  have hν1 := hev.comp_holderOnWith hCν
  have hμ1 := hev.comp_holderOnWith hCμ
  obtain ⟨Dν, hDν⟩ := hbd hν1
  obtain ⟨Dμ, hDμ⟩ := hbd hμ1
  refine ⟨_, ((hjc.smul_of_norm_le hν1 (Mc := ‖(j : ℂ)‖₊ * Dc j) (Mf := Dν)
    (fun z hz ↦ ?_) hDν).add (hCS.smul_of_norm_le hμ1 hDS hDμ)).neg.congr fun z _ ↦ ?_⟩
  · rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hDc j hj z hz) (norm_nonneg _)
  · simp [smul_eq_mul, mul_comm]

/-- **Hölder weak solutions of the equation of elementary symmetric functions are classical.**
Let `U ⊆ ℂ` be open, `0 < α < 1`, and for `z ∈ U` let `R z` be a multiset of `m` complex numbers
with elementary symmetric functions `c_j(z) = e_j(R z)`, `1 ≤ j ≤ m`, `α`-Hölder on every compact
subset of `U`. Let the `(0,1)`-forms `ν` and `μ` be `(α / m)`-Hölder on every compact subset of
`U`. If the `c_j` solve

`\bar∂ c_j + j ν c_j + μ ∑_{w ∈ R} \bar w e_{j-1}(R ∖ w) = 0`

in the sense of distributions on `U`, then each `c_j` is `C¹` on `U`, solves the equation at every
point of `U`, and has `(α / m)`-Hölder derivative on every compact subset of `U`. -/
theorem contDiffOn_and_conjWirtingerDeriv_add_add_eq_zero_of_esymm {m : ℕ} {α : ℝ≥0}
    (hα : 0 < α) (hα1 : α < 1) {U : Set ℂ} (hU : IsOpen U) {c : ℕ → ℂ → ℂ}
    {R : ℂ → Multiset ℂ} {ν μ : ℂ → ℂ →L⋆[ℂ] ℂ}
    (hR : ∀ z ∈ U, Multiset.card (R z) = m ∧ ∀ j ∈ Finset.Icc 1 m, c j z = (R z).esymm j)
    (hc : ∀ j ∈ Finset.Icc 1 m, ∀ K ⊆ U, IsCompact K → ∃ C, HolderOnWith C α (c j) K)
    (hν : ∀ K ⊆ U, IsCompact K → ∃ C, HolderOnWith C (α / m) ν K)
    (hμ : ∀ K ⊆ U, IsCompact K → ∃ C, HolderOnWith C (α / m) μ K)
    (hweak : ∀ j ∈ Finset.Icc 1 m, HasWeakConjWirtingerDerivOn volume ⟨U, hU⟩ (c j) fun z ↦
      -((j * c j z) • ν z +
        ((R z).map fun w ↦ conj w * ((R z).erase w).esymm (j - 1)).sum • μ z) 1) :
    ∀ j ∈ Finset.Icc 1 m, ContDiffOn ℝ 1 (c j) U ∧
      (∀ z ∈ U, conjWirtingerDeriv (c j) z + (j * c j z) • ν z +
        ((R z).map fun w ↦ conj w * ((R z).erase w).esymm (j - 1)).sum • μ z = 0) ∧
      ∀ K ⊆ U, IsCompact K → ∃ C, HolderOnWith C (α / m) (fderiv ℝ (c j)) K := by
  intro j hj
  have hm : m ≠ 0 := by have := Finset.mem_Icc.1 hj; omega
  have hβ : 0 < α / m := div_pos hα (by exact_mod_cast Nat.pos_of_ne_zero hm)
  have hβ1 : α / m < 1 := (div_le_self zero_le
    (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hm)).trans_lt hα1
  -- the right side is `(α / m)`-Hölder on compact sets, so the Schauder estimate applies
  obtain ⟨hcd, hcl, hcH⟩ := (hweak j hj).contDiffOn_one_of_holderOnWith hβ hβ1
    (continuousOn_of_forall_isCompact_holderOnWith hU hα (hc j hj)) fun K hKU hK ↦
      exists_holderOnWith_neg_smul_add_smul_apply_one hj hK (fun z hz ↦ hR z (hKU hz))
        (fun i hi ↦ hc i hi K hKU hK) (hν K hKU hK) (hμ K hKU hK)
  refine ⟨hcd, fun z hz ↦ ContinuousLinearMap.coe_injective (LinearMap.ext_ring ?_), hcH⟩
  simp only [ContinuousLinearMap.coe_coe, add_apply, hcl z hz, ContinuousLinearMap.toLinearMap_zero,
    LinearMap.zero_apply]
  ring

/-- **Subsequential limits of the coefficients are classical solutions.** Under the hypotheses of
`TauCeti.exists_strictMono_hasWeakConjWirtingerDerivOn_of_esymm`, suppose moreover that the limit
forms `ν₀` and `μ₀` are Hölder of exponent `(1 - 2 / p) / m` on every compact subset of `U`, as
smooth forms are. Then along a subsequence every `b n j`, `1 ≤ j ≤ m`, converges locally uniformly
on `U` to a limit `c j` that is `C¹` on `U`; the `c j` are the elementary symmetric functions of
multisets `R₀ z` of `m` complex numbers, and they solve

`\bar∂ c_j + j ν₀ c_j + μ₀ ∑_{V ∈ R₀} \bar V e_{j-1}(R₀ ∖ V) = 0`

at every point of `U`. -/
theorem exists_strictMono_contDiffOn_of_esymm {m : ℕ} {p : ℝ≥0} (hp : 2 < p)
    {U : Set ℂ} (hU : IsOpen U) {ρ Λ : ℝ≥0} {b : ℕ → ℕ → ℂ → ℂ} {R : ℕ → ℂ → Multiset ℂ}
    {ν μ : ℕ → ℂ → ℂ →L⋆[ℂ] ℂ} {ν₀ μ₀ : ℂ → ℂ →L⋆[ℂ] ℂ}
    (hb : ∀ n, ∀ j ∈ Finset.Icc 1 m, ContDiffOn ℝ ∞ (b n j) U)
    (hcard : ∀ n, ∀ z ∈ U, Multiset.card (R n z) = m)
    (hbR : ∀ n, ∀ j ∈ Finset.Icc 1 m, ∀ z ∈ U, b n j z = (R n z).esymm j)
    (hρ : ∀ n, ∀ z ∈ U, ∀ w ∈ R n z, ‖w‖ ≤ ρ) (hνΛ : ∀ n, ∀ z ∈ U, ‖ν n z‖ ≤ Λ)
    (hμΛ : ∀ n, ∀ z ∈ U, ‖μ n z‖ ≤ Λ)
    (hν : TendstoLocallyUniformlyOn ν ν₀ atTop U)
    (hν₀ : ∀ K ⊆ U, IsCompact K → ∃ C, HolderOnWith C ((1 - 2 / p) / m) ν₀ K)
    (hμ : TendstoLocallyUniformlyOn μ μ₀ atTop U)
    (hμ₀ : ∀ K ⊆ U, IsCompact K → ∃ C, HolderOnWith C ((1 - 2 / p) / m) μ₀ K)
    (hr : ∀ K ⊆ U, IsCompact K → ∃ B : ℝ≥0, ∀ n, ∀ j ∈ Finset.Icc 1 m,
      eLpNorm (fun z ↦ (conjWirtingerDeriv (b n j) z + (j * b n j z) • ν n z +
        ((R n z).map fun w ↦ conj w * ((R n z).erase w).esymm (j - 1)).sum • μ n z) 1)
          p (volume.restrict K) ≤ B)
    (hr₀ : ∀ K ⊆ U, IsCompact K → ∀ j ∈ Finset.Icc 1 m,
      Tendsto (fun n ↦ ∫⁻ z in K, ‖(conjWirtingerDeriv (b n j) z + (j * b n j z) • ν n z +
        ((R n z).map fun w ↦ conj w * ((R n z).erase w).esymm (j - 1)).sum • μ n z) 1‖ₑ)
          atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c : ℕ → ℂ → ℂ, ∃ R₀ : ℂ → Multiset ℂ,
      (∀ j ∈ Finset.Icc 1 m, TendstoLocallyUniformlyOn (fun n ↦ b (φ n) j) (c j) atTop U ∧
        ContDiffOn ℝ 1 (c j) U) ∧
      (∀ z ∈ U, Multiset.card (R₀ z) = m ∧ ∀ j ∈ Finset.Icc 1 m, c j z = (R₀ z).esymm j) ∧
      ∀ j ∈ Finset.Icc 1 m, ∀ z ∈ U, conjWirtingerDeriv (c j) z + (j * c j z) • ν₀ z +
        ((R₀ z).map fun w ↦ conj w * ((R₀ z).erase w).esymm (j - 1)).sum • μ₀ z = 0 := by
  -- the forms `ν₀` and `μ₀` are continuous, being Hölder on compact sets
  have hp0 : (0 : ℝ≥0) < p := zero_lt_two.trans hp
  have hα : 0 < 1 - 2 / p := tsub_pos_of_lt ((div_lt_one hp0).2 hp)
  have hα1 : 1 - 2 / p < 1 := tsub_lt_self one_pos (div_pos two_pos hp0)
  have hβ (hm : m ≠ 0) : 0 < (1 - 2 / p) / m :=
    div_pos hα (by exact_mod_cast Nat.pos_of_ne_zero hm)
  rcases eq_or_ne m 0 with rfl | hm
  · exact ⟨id, strictMono_id, 0, fun _ ↦ 0, by simp, by simp, by simp⟩
  obtain ⟨φ, hφ, c, R₀, hc, hR₀, hweak⟩ := exists_strictMono_hasWeakConjWirtingerDerivOn_of_esymm
    hp hU hb hcard hbR hρ hνΛ hμΛ hν
    (continuousOn_of_forall_isCompact_holderOnWith hU (hβ hm) hν₀) hμ
    (continuousOn_of_forall_isCompact_holderOnWith hU (hβ hm) hμ₀) hr hr₀
  have hreg := contDiffOn_and_conjWirtingerDeriv_add_add_eq_zero_of_esymm hα hα1 hU hR₀
    (fun j hj K hKU hK ↦ (hc j hj).2 K hK hKU) hν₀ hμ₀ hweak
  exact ⟨φ, hφ, c, R₀, fun j hj ↦ ⟨(hc j hj).1, (hreg j hj).1⟩, hR₀,
    fun j hj ↦ (hreg j hj).2.1⟩

end TauCeti
