/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Compactness
public import TauCeti.Analysis.Complex.Wirtinger.Weak
public import TauCeti.Analysis.Polynomial.SymmetricPower
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import TauCeti.Analysis.Complex.Wirtinger.NewtonIdentities
import TauCeti.Analysis.Complex.Wirtinger.Precompact
import TauCeti.Analysis.Polynomial.Monic.RootBound
import TauCeti.Order.Filter.AtTopBot
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.Lebesgue.UniformConvergence
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Compactness of coefficients solving the equation of elementary symmetric functions, and limits

Let `D = \bar∂ + ν W + μ \bar W` be a real Cauchy–Riemann operator on a complex line over a domain
`U ⊆ ℂ`, with `(0,1)`-forms `ν` and `μ`. If `m` points `R(z)` of the fibre over `z` move by
solutions of `D`, their elementary symmetric functions `b_j(z) = e_j(R(z))` satisfy

`\bar∂ b_j + j ν b_j + μ ∑_{V ∈ R} \bar V e_{j-1}(R ∖ V) = 0`,  `1 ≤ j ≤ m`.

In Taubes's analysis of Seiberg–Witten solutions concentrating along a pseudoholomorphic curve,
the `b_j` are the Newton coefficients of the normal moments of the curvature current, and they
satisfy this equation only up to remainders `r_j`
(`TauCeti.conjWirtingerDeriv_add_esymm_erase_eq_of_newton` gives the equation with its explicit
remainder). Bounds on the `r_j` in `L^{p_m}`, `p_m = 2 + 2 / m`, come from Taubes's estimates for
the Seiberg–Witten equations; here they are a hypothesis. The roots `R(z)` of the polynomial
`Wᵐ - b₁ Wᵐ⁻¹ + ⋯ + (-1)ᵐ bₘ` stay in a fixed disc, by the bounds of
`TauCeti.norm_le_of_mem_roots_newtonPolynomial_integral_pow_sub`.

This file proves that such coefficient families are precompact. For a sequence of families with
roots in a fixed disc, bounded `ν` and `μ`, and remainders bounded in `Lᵖ` on each compact subset
of `U` for some `p > 2`, a subsequence of every coefficient `b_j` converges locally uniformly on
`U`, and the limits are Hölder continuous with exponent `1 - 2 / p` on compact subsets of `U`
(`TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_of_esymm`). For `p = p_m` the exponent is
`1 / (m + 1)` (`TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_of_esymm_of_eq`), the Morrey
exponent of `W^{1, p_m}` in the plane.

The roots bound the coefficients and the zeroth-order terms of the equation
(`Multiset.norm_esymm_le`), so `\bar∂ b_j` differs from the remainder by a uniformly bounded
term. It is therefore bounded in `Lᵖ` on each compact subset of `U`
(`TauCeti.eLpNorm_conjWirtingerDeriv_restrict_le_of_norm_sub_le`), and each coefficient sequence is
precompact by `TauCeti.exists_subseq_tendstoLocallyUniformlyOn_of_eLpNorm_conjWirtingerDeriv_le`.
A common subsequence for the finitely many coefficients is extracted one coefficient at a time
(`TauCeti.extraction_forall_mem_finset`).

**The limiting equation.** If the remainders `r_j` moreover tend to zero in `L¹` on compact
subsets of `U`, and `ν`, `μ` converge locally uniformly to continuous limits `ν₀`, `μ₀`, then the
limits `c_j` of the coefficients solve the equation exactly, in the distributional sense:

`\bar∂ c_j + j ν₀ c_j + μ₀ ∑_{V ∈ R₀} \bar V e_{j-1}(R₀ ∖ V) = 0`,

where `R₀(z)` is the multiset of the `m` roots of `Wᵐ - c₁ Wᵐ⁻¹ + ⋯ + (-1)ᵐ cₘ`
(`TauCeti.exists_hasWeakConjWirtingerDerivOn_of_tendstoLocallyUniformlyOn_esymm`). This is the
equation of the elementary symmetric functions of `m` solutions of `D`, which the root branches of
`TauCeti.Analysis.Complex.Wirtinger.Root.Branch` and their normalization across collisions take
as input, there for `C¹` coefficients solving it classically; when the limit forms `ν₀` and `μ₀`
are Hölder of exponent `(1 - 2 / p) / m` on compact sets, that the limits have this regularity is
`TauCeti.exists_strictMono_contDiffOn_of_esymm`, in
`TauCeti.Analysis.Complex.Wirtinger.Regularity.CoefficientEquation`. The zeroth-order term
`∑_{V ∈ R} \bar V e_{j-1}(R ∖ V)` is a continuous function of the unordered tuple `R ∈ Sym ℂ m`
(`TauCeti.continuous_sum_map_conj_mul_esymm_erase`), hence of the coefficients, through the
elementary symmetric chart `Sym.coeffHomeomorph`; so it converges
locally uniformly with them (`TauCeti.tendstoLocallyUniformlyOn_sum_map_conj_mul_esymm_erase`).
The classical derivatives `\bar∂ b_j` then converge in `L¹` on compact sets to the zeroth-order
term of the limit, and the weak equation passes to the limit
(`TauCeti.hasWeakConjWirtingerDerivOn_of_tendsto_setLIntegral_enorm_sub`). Together with the
compactness above, a subsequence of the coefficients converges to Hölder continuous solutions of
the limiting equation (`TauCeti.exists_strictMono_hasWeakConjWirtingerDerivOn_of_esymm`).

**Change of frame.** The `Lᵖ(K)` norms of the remainders in two frames of the normal line are
comparable. Under a change of frame `W ↦ g W` with `c ≤ |g| ≤ G` on a measurable set `K`, the
remainders in the two frames, related by the factor `gʲ`
(`TauCeti.conjWirtingerDeriv_pow_mul_add_add_esymm_erase_eq_pow_smul`), have `Lᵖ(K)` norms within
the factors `Gʲ` and `c⁻ʲ` of each other
(`TauCeti.eLpNorm_conjWirtingerDeriv_pow_mul_add_add_esymm_erase_le`,
`TauCeti.eLpNorm_conjWirtingerDeriv_add_add_esymm_erase_le`). For a frame continuous and
nonvanishing on a neighbourhood of a compact set such bounds hold on it.

## Main results

* `TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_of_esymm`: locally uniform convergence of
  a subsequence of the coefficients, with Hölder continuous limits of exponent `1 - 2 / p`.
* `TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_of_esymm_of_eq`: the same for
  `p = 2 + 2 / m`, with Hölder exponent `1 / (m + 1)`.
* `TauCeti.norm_sum_map_conj_mul_esymm_erase_le`: the zeroth-order term of the equation is
  bounded by the roots.
* `TauCeti.continuous_sum_map_conj_mul_esymm_erase`: the zeroth-order term of the equation is
  continuous on `Sym ℂ m`.
* `TauCeti.continuousOn_sum_map_conj_mul_esymm_erase`,
  `TauCeti.tendstoLocallyUniformlyOn_sum_map_conj_mul_esymm_erase`: it is continuous in, and
  converges locally uniformly with, the elementary symmetric functions.
* `TauCeti.exists_hasWeakConjWirtingerDerivOn_of_tendstoLocallyUniformlyOn_esymm`: locally
  uniform limits of the coefficients solve the limiting equation weakly.
* `TauCeti.exists_strictMono_hasWeakConjWirtingerDerivOn_of_esymm`: a subsequence converges to
  Hölder continuous weak solutions of the limiting equation.
* `TauCeti.eLpNorm_conjWirtingerDeriv_pow_mul_add_add_esymm_erase_le`,
  `TauCeti.eLpNorm_conjWirtingerDeriv_add_add_esymm_erase_le`: the `Lᵖ` norms of the remainders
  in two frames are comparable.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open scoped ENNReal NNReal ContDiff ComplexConjugate Topology
open MeasureTheory Set Filter

namespace TauCeti

/-- **The zeroth-order term is bounded by the roots.** If a multiset `s` has at most `m` elements,
all of norm at most `ρ`, then `‖∑_{w ∈ s} \bar w e_k(s ∖ w)‖ ≤ m ρ C(m, k) ρᵏ`. -/
theorem norm_sum_map_conj_mul_esymm_erase_le {m k : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) {s : Multiset ℂ}
    (hcard : Multiset.card s ≤ m) (hρ : ∀ w ∈ s, ‖w‖ ≤ ρ) :
    ‖(s.map fun w ↦ conj w * (s.erase w).esymm k).sum‖ ≤ m * ρ * (m.choose k * ρ ^ k) := by
  refine (norm_multiset_sum_le _).trans ?_
  rw [Multiset.map_map]
  refine (Multiset.sum_le_card_nsmul _ (ρ * (m.choose k * ρ ^ k)) fun r hr ↦ ?_).trans ?_
  · obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hr
    rw [Function.comp_apply, norm_mul, Complex.norm_conj]
    -- the elementary symmetric functions of `s ∖ w` are bounded by the roots
    refine mul_le_mul (hρ w hw) ((Multiset.norm_esymm_le (fun v hv ↦
      hρ v (Multiset.mem_of_mem_erase hv)) k).trans ?_) (norm_nonneg _) hρ0
    gcongr
    exact Multiset.card_erase_le.trans hcard
  · rw [Multiset.card_map, nsmul_eq_mul, mul_assoc]
    gcongr

/-- The zeroth-order terms of the equation of the elementary symmetric functions are bounded by
the roots: if `R` has at most `m` elements, all of norm at most `ρ`, `b z = e_j(R)` with
`1 ≤ j ≤ m`, and `‖ν‖, ‖μ‖ ≤ Λ`, then `\bar∂b` differs from
`(\bar∂b + j ν b + μ ∑_{V ∈ R} \bar V e_{j-1}(R ∖ V))(1)` by at most
`j C(m, j) ρʲ Λ + m ρ C(m, j - 1) ρ^(j-1) Λ`. -/
private theorem norm_conjWirtingerDeriv_sub_le_of_esymm {m j : ℕ} {ρ Λ : ℝ≥0} {b : ℂ → ℂ}
    {R : Multiset ℂ} {z : ℂ} {ν μ : ℂ →L⋆[ℂ] ℂ} (hcard : Multiset.card R ≤ m)
    (hbR : b z = R.esymm j) (hρ : ∀ w ∈ R, ‖w‖ ≤ ρ) (hν : ‖ν‖ ≤ Λ) (hμ : ‖μ‖ ≤ Λ) :
    ‖conjWirtingerDeriv b z 1 - (conjWirtingerDeriv b z + (j * b z) • ν +
      (R.map fun w ↦ conj w * (R.erase w).esymm (j - 1)).sum • μ) 1‖ ≤
        j * (m.choose j * ρ ^ j) * Λ + m * ρ * (m.choose (j - 1) * ρ ^ (j - 1)) * Λ := by
  have hsum := norm_sum_map_conj_mul_esymm_erase_le (k := j - 1) ρ.coe_nonneg hcard hρ
  have hν1 : ‖ν 1‖ ≤ Λ := by simpa using ν.le_opNorm 1 |>.trans (by simpa using hν)
  have hμ1 : ‖μ 1‖ ≤ Λ := by simpa using μ.le_opNorm 1 |>.trans (by simpa using hμ)
  calc ‖conjWirtingerDeriv b z 1 - (conjWirtingerDeriv b z + (j * b z) • ν +
        (R.map fun w ↦ conj w * (R.erase w).esymm (j - 1)).sum • μ) 1‖
      = ‖(j * b z) * ν 1 + (R.map fun w ↦ conj w * (R.erase w).esymm (j - 1)).sum * μ 1‖ := by
        rw [← norm_neg]
        simp only [add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
        ring_nf
    _ ≤ _ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, norm_mul, Complex.norm_natCast, hbR]
          gcongr
          exact (Multiset.norm_esymm_le hρ j).trans (by gcongr)
        · rw [norm_mul]
          gcongr

/-- **Precompactness of coefficients solving the equation of elementary symmetric functions.**
Let `2 < p < ∞` and let `U ⊆ ℂ` be open. For each `n` let `R n z` be a multiset of at most `m`
complex numbers of norm at most `ρ`, for `z ∈ U`, let `b n j` be smooth on `U` and equal to the
`j`-th elementary symmetric function of `R n z` there, for `1 ≤ j ≤ m`, and let `ν n`, `μ n` be
`(0,1)`-forms of norm at most `Λ` on `U`. Suppose the remainders

`r_j = \bar∂ b_j + j ν b_j + μ ∑_{V ∈ R} \bar V e_{j-1}(R ∖ V)`

are bounded in `Lᵖ` on each compact subset of `U`, uniformly in `n`. Then along a subsequence
every `b n j`, `1 ≤ j ≤ m`, converges locally uniformly on `U`, to a limit that is Hölder
continuous with exponent `1 - 2 / p` on each compact subset of `U`. -/
theorem exists_strictMono_tendstoLocallyUniformlyOn_of_esymm {m : ℕ} {p : ℝ≥0} (hp : 2 < p)
    {U : Set ℂ} (hU : IsOpen U) {ρ Λ : ℝ≥0} {b : ℕ → ℕ → ℂ → ℂ} {R : ℕ → ℂ → Multiset ℂ}
    {ν μ : ℕ → ℂ → ℂ →L⋆[ℂ] ℂ} (hb : ∀ n, ∀ j ∈ Finset.Icc 1 m, ContDiffOn ℝ ∞ (b n j) U)
    (hcard : ∀ n, ∀ z ∈ U, Multiset.card (R n z) ≤ m)
    (hbR : ∀ n, ∀ j ∈ Finset.Icc 1 m, ∀ z ∈ U, b n j z = (R n z).esymm j)
    (hρ : ∀ n, ∀ z ∈ U, ∀ w ∈ R n z, ‖w‖ ≤ ρ) (hν : ∀ n, ∀ z ∈ U, ‖ν n z‖ ≤ Λ)
    (hμ : ∀ n, ∀ z ∈ U, ‖μ n z‖ ≤ Λ)
    (hr : ∀ K ⊆ U, IsCompact K → ∃ B : ℝ≥0, ∀ n, ∀ j ∈ Finset.Icc 1 m,
      eLpNorm (fun z ↦ (conjWirtingerDeriv (b n j) z + (j * b n j z) • ν n z +
        ((R n z).map fun w ↦ conj w * ((R n z).erase w).esymm (j - 1)).sum • μ n z) 1)
          p (volume.restrict K) ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c : ℕ → ℂ → ℂ, ∀ j ∈ Finset.Icc 1 m,
      TendstoLocallyUniformlyOn (fun n ↦ b (φ n) j) (c j) atTop U ∧
      ∀ K, IsCompact K → K ⊆ U → ∃ C : ℝ≥0, HolderOnWith C (1 - 2 / p) (c j) K := by
  -- Each coefficient is precompact along any subsequence.
  have h : ∀ j ∈ Finset.Icc 1 m, ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ v : ℂ → ℂ, TendstoLocallyUniformlyOn (fun n ↦ b ((φ ∘ ψ) n) j) v atTop U ∧
        ∀ K, IsCompact K → K ⊆ U → ∃ C : ℝ≥0, HolderOnWith C (1 - 2 / p) v K := by
    intro j hj φ _
    -- On a compact `K ⊆ U`, `\bar∂ b_j` is bounded in `Lᵖ(K)`.
    have hdbar (K : Set ℂ) (hKU : K ⊆ U) (hK : IsCompact K) : ∃ A : ℝ≥0∞, A ≠ (∞ : ℝ≥0∞) ∧
        ∀ n, eLpNorm (fun z ↦ conjWirtingerDeriv (b (φ n) j) z 1) p (volume.restrict K) ≤ A := by
      obtain ⟨B, hB⟩ := hr K hKU hK
      refine ⟨_, by simp [ENNReal.mul_ne_top, hK.measure_lt_top.ne], fun n ↦
        eLpNorm_conjWirtingerDeriv_restrict_le_of_norm_sub_le
          (by exact_mod_cast one_le_two.trans hp.le) hU hK.measurableSet hKU (hb (φ n) _ hj)
          (fun z hz ↦
            norm_conjWirtingerDeriv_sub_le_of_esymm (hcard (φ n) z (hKU hz))
              (hbR (φ n) _ hj z (hKU hz)) (hρ (φ n) z (hKU hz)) (hν (φ n) z (hKU hz))
              (hμ (φ n) z (hKU hz))) (hB (φ n) j hj)⟩
    obtain ⟨ψ, hψ, v, -, hv, hvH⟩ :=
      exists_subseq_tendstoLocallyUniformlyOn_of_eLpNorm_conjWirtingerDeriv_le (F := ℂ) hp hU
        (u := fun n ↦ b (φ n) j) (fun n ↦ hb (φ n) _ hj)
        (fun _ hKU _ ↦ ⟨m.choose j * ρ ^ j, fun n z hz ↦ by
          rw [hbR _ _ hj z (hKU hz)]
          exact (Multiset.norm_esymm_le (hρ _ z (hKU hz)) _).trans
            (by gcongr; exact hcard _ z (hKU hz))⟩)
        hdbar
    exact ⟨ψ, hψ, v, hv, fun K hK hKU ↦ hvH K hKU hK⟩
  -- Extract one common subsequence.
  obtain ⟨φ, hφ, hc⟩ := extraction_forall_mem_finset (P := fun j φ ↦ ∃ v : ℂ → ℂ,
      TendstoLocallyUniformlyOn (fun n ↦ b (φ n) j) v atTop U ∧
        ∀ K, IsCompact K → K ⊆ U → ∃ C : ℝ≥0, HolderOnWith C (1 - 2 / p) v K) h
    fun j _ φ ψ hψ ⟨v, hv, hvH⟩ ↦ ⟨v, hv.comp_tendsto hψ.tendsto_atTop, hvH⟩
  choose! c hc using hc
  exact ⟨φ, hφ, c, hc⟩

/-- **The Morrey exponent `1 / (m + 1)`.** For `p = 2 + 2 / m`, the exponent of
`TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_of_esymm`, the coefficients `b_j`,
`1 ≤ j ≤ m`, have a subsequence converging locally uniformly on `U` to limits that are Hölder
continuous with exponent `1 / (m + 1)` on each compact subset of `U`. -/
theorem exists_strictMono_tendstoLocallyUniformlyOn_of_esymm_of_eq {m : ℕ} {p : ℝ≥0}
    (hpm : p = 2 + 2 / m) {U : Set ℂ} (hU : IsOpen U) {ρ Λ : ℝ≥0}
    {b : ℕ → ℕ → ℂ → ℂ} {R : ℕ → ℂ → Multiset ℂ} {ν μ : ℕ → ℂ → ℂ →L⋆[ℂ] ℂ}
    (hb : ∀ n, ∀ j ∈ Finset.Icc 1 m, ContDiffOn ℝ ∞ (b n j) U)
    (hcard : ∀ n, ∀ z ∈ U, Multiset.card (R n z) ≤ m)
    (hbR : ∀ n, ∀ j ∈ Finset.Icc 1 m, ∀ z ∈ U, b n j z = (R n z).esymm j)
    (hρ : ∀ n, ∀ z ∈ U, ∀ w ∈ R n z, ‖w‖ ≤ ρ) (hν : ∀ n, ∀ z ∈ U, ‖ν n z‖ ≤ Λ)
    (hμ : ∀ n, ∀ z ∈ U, ‖μ n z‖ ≤ Λ)
    (hr : ∀ K ⊆ U, IsCompact K → ∃ B : ℝ≥0, ∀ n, ∀ j ∈ Finset.Icc 1 m,
      eLpNorm (fun z ↦ (conjWirtingerDeriv (b n j) z + (j * b n j z) • ν n z +
        ((R n z).map fun w ↦ conj w * ((R n z).erase w).esymm (j - 1)).sum • μ n z) 1)
          p (volume.restrict K) ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c : ℕ → ℂ → ℂ, ∀ j ∈ Finset.Icc 1 m,
      TendstoLocallyUniformlyOn (fun n ↦ b (φ n) j) (c j) atTop U ∧
      ∀ K, IsCompact K → K ⊆ U → ∃ C : ℝ≥0, HolderOnWith C (1 / (m + 1)) (c j) K := by
  -- For `m = 0` there are no coefficients.
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨id, strictMono_id, 0, by simp⟩
  have hp : 2 < p := by
    rw [hpm]
    exact lt_add_of_pos_right 2 (by positivity)
  have hexp : (1 - 2 / p : ℝ≥0) = 1 / (m + 1) := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    rw [← NNReal.coe_inj, NNReal.coe_sub ((div_le_one₀ (zero_lt_two.trans hp)).2 hp.le), hpm]
    push_cast
    field_simp
    ring
  rw [← hexp]
  exact exists_strictMono_tendstoLocallyUniformlyOn_of_esymm hp hU hb hcard hbR hρ hν hμ hr

/-! ### The limiting equation -/

/-- **The zeroth-order term of the equation is continuous in the roots.** For every `k`, the
function `R ↦ ∑_{w ∈ R} \bar w e_k(R ∖ w)` on unordered `m`-tuples of complex numbers is continuous
for the quotient topology of `Sym ℂ m`. Through the elementary symmetric chart
`Sym.coeffHomeomorph`, it is therefore a continuous function of the coefficients `e_j(R)`. -/
theorem continuous_sum_map_conj_mul_esymm_erase (m k : ℕ) :
    Continuous fun s : Sym ℂ m ↦
      ((s : Multiset ℂ).map fun w ↦ conj w * ((s : Multiset ℂ).erase w).esymm k).sum := by
  refine Sym.continuous_iff_comp_ofFn.2 ?_
  -- On an ordered tuple `f`, the term is the sum over `i` of `\bar fᵢ` times `e_k` of the
  -- entries of `f` other than the `i`-th.
  have key (f : Fin m → ℂ) :
      (((Sym.ofFn f : Sym ℂ m) : Multiset ℂ).map fun w ↦
          conj w * (((Sym.ofFn f : Sym ℂ m) : Multiset ℂ).erase w).esymm k).sum =
        ∑ i, conj (f i) * ∑ t ∈ (Finset.univ.erase i).powersetCard k, ∏ l ∈ t, f l := by
    rw [Sym.coe_ofFn, ← Fin.univ_val_map, Multiset.map_map, Finset.sum_eq_multiset_sum]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun i _ ↦ ?_)
    rw [Function.comp_apply,
      ← Multiset.map_erase_of_mem f _ (by simp : i ∈ (Finset.univ : Finset (Fin m)).val),
      ← Finset.erase_val, Finset.esymm_map_val]
  simp only [Function.comp_def, key]
  fun_prop

/-- **The zeroth-order term through the elementary symmetric chart.** There is a continuous function
`Φ` of `m` coefficients such that, for every `m`-element multiset `s`, the term
`∑_{w ∈ s} \bar w e_k(s ∖ w)` is `Φ` of the signed coefficients `(-1)^(m-i) e_{m-i}(s)` of `s`. -/
private theorem exists_continuous_sum_map_conj_mul_esymm_erase_eq (m k : ℕ) :
    ∃ Φ : (Fin m → ℂ) → ℂ, Continuous Φ ∧ ∀ s : Multiset ℂ, Multiset.card s = m →
      (s.map fun w ↦ conj w * (s.erase w).esymm k).sum =
        Φ fun i ↦ (-1) ^ (m - (i : ℕ)) * s.esymm (m - i) :=
  ⟨fun v ↦ (((Sym.coeffHomeomorph ℂ m).symm v : Multiset ℂ).map
      fun w ↦ conj w * (((Sym.coeffHomeomorph ℂ m).symm v : Multiset ℂ).erase w).esymm k).sum,
    (continuous_sum_map_conj_mul_esymm_erase m k).comp (Sym.coeffHomeomorph ℂ m).symm.continuous,
    fun s hs ↦ by
      simp only [Sym.coeffHomeomorph_symm_apply, Sym.coeffEquiv_symm_esymm hs, Sym.coe_mk]⟩

/-- The signed coefficient tuple `z ↦ ((-1)^(m-i) e_{m-i}(R₀ z))ᵢ` is continuous on `U` when the
elementary symmetric functions `e_j(R₀ z)`, `1 ≤ j ≤ m`, are. -/
private theorem continuousOn_signed_esymm {m : ℕ} {U : Set ℂ} {R₀ : ℂ → Multiset ℂ}
    (hR₀ : ∀ j ∈ Finset.Icc 1 m, ContinuousOn (fun z ↦ (R₀ z).esymm j) U) :
    ContinuousOn (fun z (i : Fin m) ↦ (-1) ^ (m - (i : ℕ)) * (R₀ z).esymm (m - i)) U :=
  continuousOn_pi.2 fun i ↦ continuousOn_const.mul (hR₀ _ (Finset.mem_Icc.2 ⟨by omega, by omega⟩))

/-- **The zeroth-order term depends continuously on the coefficients.** If `R₀ z` has `m` elements
for `z ∈ U` and its elementary symmetric functions `e_j(R₀ z)`, `1 ≤ j ≤ m`, are continuous on
`U`, then so is `z ↦ ∑_{w ∈ R₀ z} \bar w e_k(R₀ z ∖ w)`. -/
theorem continuousOn_sum_map_conj_mul_esymm_erase {m k : ℕ} {U : Set ℂ} {R₀ : ℂ → Multiset ℂ}
    (hcard : ∀ z ∈ U, Multiset.card (R₀ z) = m)
    (hR₀ : ∀ j ∈ Finset.Icc 1 m, ContinuousOn (fun z ↦ (R₀ z).esymm j) U) :
    ContinuousOn (fun z ↦ ((R₀ z).map fun w ↦ conj w * ((R₀ z).erase w).esymm k).sum) U := by
  obtain ⟨Φ, hΦ, hΦR⟩ := exists_continuous_sum_map_conj_mul_esymm_erase_eq m k
  exact (hΦ.comp_continuousOn (continuousOn_signed_esymm hR₀)).congr fun z hz ↦ hΦR _ (hcard z hz)

/-- **The zeroth-order term converges with the coefficients.** Let `R n z` and `R₀ z` have `m`
elements for `z ∈ U`, an open set. If the elementary symmetric functions `e_j(R n z)` converge
locally uniformly on `U` to `e_j(R₀ z)`, `1 ≤ j ≤ m`, and these limits are continuous on `U`, then
`∑_{w ∈ R n z} \bar w e_k(R n z ∖ w)` converges locally uniformly on `U` to
`∑_{w ∈ R₀ z} \bar w e_k(R₀ z ∖ w)`. -/
theorem tendstoLocallyUniformlyOn_sum_map_conj_mul_esymm_erase {ι : Type*} {l : Filter ι}
    {m k : ℕ} {U : Set ℂ} (hU : IsOpen U) {R : ι → ℂ → Multiset ℂ} {R₀ : ℂ → Multiset ℂ}
    (hcard : ∀ n, ∀ z ∈ U, Multiset.card (R n z) = m)
    (hcard₀ : ∀ z ∈ U, Multiset.card (R₀ z) = m)
    (hR : ∀ j ∈ Finset.Icc 1 m,
      TendstoLocallyUniformlyOn (fun n z ↦ (R n z).esymm j) (fun z ↦ (R₀ z).esymm j) l U)
    (hR₀ : ∀ j ∈ Finset.Icc 1 m, ContinuousOn (fun z ↦ (R₀ z).esymm j) U) :
    TendstoLocallyUniformlyOn
      (fun n z ↦ ((R n z).map fun w ↦ conj w * ((R n z).erase w).esymm k).sum)
      (fun z ↦ ((R₀ z).map fun w ↦ conj w * ((R₀ z).erase w).esymm k).sum) l U := by
  have hmem (i : Fin m) : m - (i : ℕ) ∈ Finset.Icc 1 m := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  -- Read both sides through the coefficient tuples of the elementary symmetric chart.
  obtain ⟨Φ, hΦ, hΦR⟩ := exists_continuous_sum_map_conj_mul_esymm_erase_eq m k
  set β : ι → ℂ → Fin m → ℂ := fun n z i ↦ (-1) ^ (m - (i : ℕ)) * (R n z).esymm (m - i)
  set γ : ℂ → Fin m → ℂ := fun z i ↦ (-1) ^ (m - (i : ℕ)) * (R₀ z).esymm (m - i)
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).2 fun K hKU hK ↦ ?_
  have hβ : TendstoUniformlyOn β γ l K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Filter.eventually_all.2 fun i : Fin m ↦ Metric.tendstoUniformlyOn_iff.1
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 (hR _ (hmem i)) K hKU hK) ε hε]
      with n hn z hz
    refine (dist_pi_lt_iff hε).2 fun i ↦ ?_
    simpa [β, γ, dist_eq_norm, ← mul_sub, norm_mul, norm_pow] using hn i z hz
  have hγ : ContinuousOn γ K := (continuousOn_signed_esymm hR₀).mono hKU
  exact ((hK.image_of_continuousOn hγ).comp_tendstoUniformlyOn (fun _ _ ↦ hΦ.continuousAt)
    hβ).congr (.of_forall fun n z hz ↦ (hΦR _ (hcard n z (hKU hz))).symm) |>.congr_right
      fun z hz ↦ (hΦR _ (hcard₀ z (hKU hz))).symm

/-- **The equation of elementary symmetric functions passes to locally uniform limits.** Let
`U ⊆ ℂ` be open. Along a filter `l`, let `R n z` be a multiset of exactly `m` complex numbers, for
`z ∈ U`, let `b n j` be `C¹` on `U` and equal to the `j`-th elementary symmetric function of
`R n z` there, for `1 ≤ j ≤ m`, and let `ν n`, `μ n` be `(0,1)`-forms converging locally uniformly
on `U` to continuous `ν₀`, `μ₀`. Suppose every `b n j` converges locally uniformly on `U` to a
function `c j`, and the remainders

`r_j = \bar∂ b_j + j ν b_j + μ ∑_{V ∈ R} \bar V e_{j-1}(R ∖ V)`

tend to zero in `L¹` on each compact subset of `U`. Then the `c j` are the elementary symmetric
functions of multisets `R₀ z` of `m` complex numbers, and they solve the limiting equation

`\bar∂ c_j + j ν₀ c_j + μ₀ ∑_{V ∈ R₀} \bar V e_{j-1}(R₀ ∖ V) = 0`,  `1 ≤ j ≤ m`,

in the distributional sense on `U`. -/
theorem exists_hasWeakConjWirtingerDerivOn_of_tendstoLocallyUniformlyOn_esymm {ι : Type*}
    {l : Filter ι} [l.NeBot] {m : ℕ} {U : Set ℂ} (hU : IsOpen U) {b : ι → ℕ → ℂ → ℂ}
    {R : ι → ℂ → Multiset ℂ} {ν μ : ι → ℂ → ℂ →L⋆[ℂ] ℂ} {ν₀ μ₀ : ℂ → ℂ →L⋆[ℂ] ℂ}
    {c : ℕ → ℂ → ℂ} (hb : ∀ n, ∀ j ∈ Finset.Icc 1 m, ContDiffOn ℝ 1 (b n j) U)
    (hcard : ∀ n, ∀ z ∈ U, Multiset.card (R n z) = m)
    (hbR : ∀ n, ∀ j ∈ Finset.Icc 1 m, ∀ z ∈ U, b n j z = (R n z).esymm j)
    (hν : TendstoLocallyUniformlyOn ν ν₀ l U) (hν₀ : ContinuousOn ν₀ U)
    (hμ : TendstoLocallyUniformlyOn μ μ₀ l U) (hμ₀ : ContinuousOn μ₀ U)
    (hc : ∀ j ∈ Finset.Icc 1 m, TendstoLocallyUniformlyOn (fun n ↦ b n j) (c j) l U)
    (hr : ∀ K ⊆ U, IsCompact K → ∀ j ∈ Finset.Icc 1 m,
      Tendsto (fun n ↦ ∫⁻ z in K, ‖(conjWirtingerDeriv (b n j) z + (j * b n j z) • ν n z +
        ((R n z).map fun w ↦ conj w * ((R n z).erase w).esymm (j - 1)).sum • μ n z) 1‖ₑ)
          l (𝓝 0)) :
    ∃ R₀ : ℂ → Multiset ℂ, (∀ z ∈ U, Multiset.card (R₀ z) = m ∧
        ∀ j ∈ Finset.Icc 1 m, c j z = (R₀ z).esymm j) ∧
      ∀ j ∈ Finset.Icc 1 m, HasWeakConjWirtingerDerivOn volume ⟨U, hU⟩ (c j) fun z ↦
        -((j * c j z) • ν₀ z +
          ((R₀ z).map fun w ↦ conj w * ((R₀ z).erase w).esymm (j - 1)).sum • μ₀ z) 1 := by
  choose s hs using fun z ↦ Sym.exists_esymm_eq (n := m) fun j ↦ c j z
  set R₀ : ℂ → Multiset ℂ := fun z ↦ (s z : Multiset ℂ)
  have hcard₀ (z : ℂ) : Multiset.card (R₀ z) = m := Sym.card_coe
  have hcR₀ (z : ℂ) (j : ℕ) (hj : j ∈ Finset.Icc 1 m) : c j z = (R₀ z).esymm j := (hs z j hj).symm
  refine ⟨R₀, fun z _ ↦ ⟨hcard₀ z, fun j hj ↦ hcR₀ z j hj⟩, fun j hj ↦ ?_⟩
  have hcU (j : ℕ) (hj : j ∈ Finset.Icc 1 m) : ContinuousOn (c j) U :=
    (hc j hj).continuousOn (.of_forall fun n ↦ (hb n j hj).continuousOn)
  have hR₀ (i : ℕ) (hi : i ∈ Finset.Icc 1 m) : ContinuousOn (fun z ↦ (R₀ z).esymm i) U :=
    (hcU i hi).congr fun z _ ↦ (hcR₀ z i hi).symm
  -- The zeroth-order term converges with the coefficients and its limit is continuous.
  have hN := tendstoLocallyUniformlyOn_sum_map_conj_mul_esymm_erase (k := j - 1) hU hcard
    (fun z _ ↦ hcard₀ z) (fun i hi ↦ ((hc i hi).congr fun n z hz ↦ hbR n i hi z hz).congr_right
      fun z _ ↦ hcR₀ z i hi) hR₀
  have hN₀ := continuousOn_sum_map_conj_mul_esymm_erase (k := j - 1) (fun z _ ↦ hcard₀ z) hR₀
  have hev := ContinuousLinearMap.lipschitzWith_apply (σ₁₂ := starRingEnd ℂ) (F := ℂ) (1 : ℂ)
  have hloc {E : Type} [UniformSpace E] {F : ι → ℂ → E} {f : ℂ → E} (K : Set ℂ) (hKU : K ⊆ U)
      (hK : IsCompact K) (h : TendstoLocallyUniformlyOn F f l U) : TendstoUniformlyOn F f l K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 h K hKU hK
  -- The classical derivatives `\bar∂ b_j` converge in `L¹` on compact sets to the limiting
  -- right side, so the weak equation passes to the limit.
  refine hasWeakConjWirtingerDerivOn_of_tendsto_setLIntegral_enorm_sub (u := fun n ↦ b n j)
    (u' := fun n z ↦ conjWirtingerDeriv (b n j) z 1)
    ((hcU j hj).locallyIntegrableOn hU.measurableSet) (ContinuousOn.locallyIntegrableOn
      (hev.continuous.comp_continuousOn (((continuousOn_const.mul (hcU j hj)).smul hν₀).add
        (hN₀.smul hμ₀))).neg hU.measurableSet)
    (fun n ↦ hasWeakConjWirtingerDerivOn_of_contDiffOn (hb n j hj))
    (fun K hKU hK ↦ (hloc K hKU hK (hc j hj)).tendsto_setLIntegral_enorm_sub
      hK.measure_lt_top.ne) fun K hKU hK ↦ ?_
  have hT := (hloc K hKU hK (hc j hj)).prodMk_same
    ((hev.uniformContinuous.comp_tendstoUniformlyOn (hloc K hKU hK hν)).prodMk_same
      ((hev.uniformContinuous.comp_tendstoUniformlyOn (hloc K hKU hK hμ)).prodMk_same
        (hloc K hKU hK hN)))
  have hP : Continuous fun q : ℂ × ℂ × ℂ × ℂ × ℂ ↦
      (j : ℂ) * q.2.1 * q.2.2.1 + q.2.2.2.2 * q.2.2.2.1 := by
    fun_prop
  have hA := hK.tendstoUniformlyOn_comp_prodMk_of_continuous hP
    (((hcU j hj).prodMk ((hev.continuous.comp_continuousOn hν₀).prodMk
      ((hev.continuous.comp_continuousOn hμ₀).prodMk hN₀))).mono hKU) hT
  refine hA.tendsto_setLIntegral_enorm_sub_of_le hK.measurableSet hK.measure_lt_top.ne
    (hr K hKU hK j hj) fun n z _ ↦ le_of_eq_of_le (congrArg (‖·‖ₑ) ?_) eNorm_sub_le
  simp only [Function.comp_apply, add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Subsequential limits of the coefficients solve the limiting equation.** Under the
hypotheses of `TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_of_esymm`, with `R n z` of
exactly `m` elements, suppose moreover that `ν n → ν₀` and `μ n → μ₀` locally uniformly on `U`, with
continuous limits, and that the remainders

`r_j = \bar∂ b_j + j ν b_j + μ ∑_{V ∈ R} \bar V e_{j-1}(R ∖ V)`

tend to zero in `L¹` on each compact subset of `U`. Then along a subsequence every `b n j`,
`1 ≤ j ≤ m`, converges locally uniformly on `U` to a limit `c j`, Hölder continuous with exponent
`1 - 2 / p` on each compact subset of `U`; the `c j` are the elementary symmetric functions of
multisets `R₀ z` of `m` complex numbers, and they solve

`\bar∂ c_j + j ν₀ c_j + μ₀ ∑_{V ∈ R₀} \bar V e_{j-1}(R₀ ∖ V) = 0`

in the distributional sense on `U`. -/
theorem exists_strictMono_hasWeakConjWirtingerDerivOn_of_esymm {m : ℕ} {p : ℝ≥0} (hp : 2 < p)
    {U : Set ℂ} (hU : IsOpen U) {ρ Λ : ℝ≥0} {b : ℕ → ℕ → ℂ → ℂ} {R : ℕ → ℂ → Multiset ℂ}
    {ν μ : ℕ → ℂ → ℂ →L⋆[ℂ] ℂ} {ν₀ μ₀ : ℂ → ℂ →L⋆[ℂ] ℂ}
    (hb : ∀ n, ∀ j ∈ Finset.Icc 1 m, ContDiffOn ℝ ∞ (b n j) U)
    (hcard : ∀ n, ∀ z ∈ U, Multiset.card (R n z) = m)
    (hbR : ∀ n, ∀ j ∈ Finset.Icc 1 m, ∀ z ∈ U, b n j z = (R n z).esymm j)
    (hρ : ∀ n, ∀ z ∈ U, ∀ w ∈ R n z, ‖w‖ ≤ ρ) (hνΛ : ∀ n, ∀ z ∈ U, ‖ν n z‖ ≤ Λ)
    (hμΛ : ∀ n, ∀ z ∈ U, ‖μ n z‖ ≤ Λ)
    (hν : TendstoLocallyUniformlyOn ν ν₀ atTop U) (hν₀ : ContinuousOn ν₀ U)
    (hμ : TendstoLocallyUniformlyOn μ μ₀ atTop U) (hμ₀ : ContinuousOn μ₀ U)
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
        ∀ K, IsCompact K → K ⊆ U → ∃ C : ℝ≥0, HolderOnWith C (1 - 2 / p) (c j) K) ∧
      (∀ z ∈ U, Multiset.card (R₀ z) = m ∧ ∀ j ∈ Finset.Icc 1 m, c j z = (R₀ z).esymm j) ∧
      ∀ j ∈ Finset.Icc 1 m, HasWeakConjWirtingerDerivOn volume ⟨U, hU⟩ (c j) fun z ↦
        -((j * c j z) • ν₀ z +
          ((R₀ z).map fun w ↦ conj w * ((R₀ z).erase w).esymm (j - 1)).sum • μ₀ z) 1 := by
  obtain ⟨φ, hφ, c, hc⟩ := exists_strictMono_tendstoLocallyUniformlyOn_of_esymm hp hU hb
    (fun n z hz ↦ (hcard n z hz).le) hbR hρ hνΛ hμΛ hr
  obtain ⟨R₀, hR₀, hweak⟩ := exists_hasWeakConjWirtingerDerivOn_of_tendstoLocallyUniformlyOn_esymm
    hU (b := fun n ↦ b (φ n)) (R := fun n ↦ R (φ n)) (ν := fun n ↦ ν (φ n))
    (μ := fun n ↦ μ (φ n)) (fun n j hj ↦ (hb (φ n) j hj).of_le (by simp))
    (fun n ↦ hcard (φ n)) (fun n ↦ hbR (φ n)) (hν.comp_tendsto hφ.tendsto_atTop) hν₀
    (hμ.comp_tendsto hφ.tendsto_atTop) hμ₀ (fun j hj ↦ (hc j hj).1)
    fun K hKU hK j hj ↦ (hr₀ K hKU hK j hj).comp hφ.tendsto_atTop
  exact ⟨φ, hφ, c, R₀, hc, hR₀, hweak⟩


/-! ### Comparison of the remainder bounds in two frames -/

section Frame

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [MeasurableSpace V]
  [OpensMeasurableSpace V] {j : ℕ} {g b : V → ℂ} {ν μ : V → V →L⋆[ℂ] ℂ} {R : V → Multiset ℂ}
  {K : Set V}

/-- **Comparison of the remainders in two frames, from above.** Under a change of frame
`W ↦ g W` of the normal line over a measurable set `K` of the base, as in
`TauCeti.conjWirtingerDeriv_pow_mul_add_add_esymm_erase_eq_pow_smul`, the remainder

`r_j = \bar∂ b_j + j ν b_j + μ ∑_{V ∈ R} \bar V e_{j-1}(R ∖ V)`

of the equation of the elementary symmetric functions in the new frame has `Lᵖ(K)` norm at most
`Gʲ` times that of `r_j` in the old frame, where `|g| ≤ G` on `K`. -/
theorem eLpNorm_conjWirtingerDeriv_pow_mul_add_add_esymm_erase_le (hK : MeasurableSet K)
    (hg : ∀ x ∈ K, DifferentiableAt ℝ g x) (hgK : ∀ x ∈ K, g x ≠ 0)
    (hb : ∀ x ∈ K, DifferentiableAt ℝ b x) (hj : 0 < j) {G : ℝ} (hG : ∀ x ∈ K, ‖g x‖ ≤ G)
    (p : ℝ≥0∞) (ρ : Measure V) :
    eLpNorm (fun x ↦ conjWirtingerDeriv (fun y ↦ g y ^ j * b y) x +
        (j * (g x ^ j * b x)) • (ν x - (g x)⁻¹ • conjWirtingerDeriv g x) +
        (((R x).map (g x * ·)).map fun w ↦
          conj w * (((R x).map (g x * ·)).erase w).esymm (j - 1)).sum •
          ((g x / conj (g x)) • μ x)) p (ρ.restrict K) ≤
      ENNReal.ofReal (G ^ j) * eLpNorm (fun x ↦ conjWirtingerDeriv b x + (j * b x) • ν x +
        ((R x).map fun w ↦ conj w * ((R x).erase w).esymm (j - 1)).sum • μ x) p (ρ.restrict K) := by
  rw [eLpNorm_congr_ae ((ae_restrict_mem hK).mono fun x hx ↦
    conjWirtingerDeriv_pow_mul_add_add_esymm_erase_eq_pow_smul (hg x hx) (hgK x hx) (hb x hx) hj
      (ν x) (μ x) (R x))]
  exact ContinuousOn.eLpNorm_smul_restrict_le_of_norm_le
    (fun x hx ↦ ((hg x hx).continuousAt.pow j).continuousWithinAt) hK
    (fun x hx ↦ (norm_pow (g x) j).trans_le (pow_le_pow_left₀ (norm_nonneg _) (hG x hx) j)) _ p ρ

/-- **Comparison of the remainders in two frames, from below.** Under a change of frame
`W ↦ g W` over a measurable set `K` of the base with `c ≤ |g|` on `K`, `0 < c`, the remainder

`r_j = \bar∂ b_j + j ν b_j + μ ∑_{V ∈ R} \bar V e_{j-1}(R ∖ V)`

of the equation of the elementary symmetric functions in the old frame has `Lᵖ(K)` norm at most
`c⁻ʲ` times that of the remainder in the new frame. Together with
`TauCeti.eLpNorm_conjWirtingerDeriv_pow_mul_add_add_esymm_erase_le`, the `Lᵖ` norms of the
remainders in two frames are equivalent on every compact set of the base on which `g` and `b`
are real-differentiable and `g` does not vanish. -/
theorem eLpNorm_conjWirtingerDeriv_add_add_esymm_erase_le (hK : MeasurableSet K)
    (hg : ∀ x ∈ K, DifferentiableAt ℝ g x) (hb : ∀ x ∈ K, DifferentiableAt ℝ b x) (hj : 0 < j)
    {c : ℝ} (hc : 0 < c) (hcK : ∀ x ∈ K, c ≤ ‖g x‖) (p : ℝ≥0∞) (ρ : Measure V) :
    eLpNorm (fun x ↦ conjWirtingerDeriv b x + (j * b x) • ν x +
        ((R x).map fun w ↦ conj w * ((R x).erase w).esymm (j - 1)).sum • μ x) p (ρ.restrict K) ≤
      ENNReal.ofReal (c ^ j)⁻¹ * eLpNorm (fun x ↦ conjWirtingerDeriv (fun y ↦ g y ^ j * b y) x +
        (j * (g x ^ j * b x)) • (ν x - (g x)⁻¹ • conjWirtingerDeriv g x) +
        (((R x).map (g x * ·)).map fun w ↦
          conj w * (((R x).map (g x * ·)).erase w).esymm (j - 1)).sum •
          ((g x / conj (g x)) • μ x)) p (ρ.restrict K) := by
  have hgK (x : V) (hx : x ∈ K) : g x ≠ 0 := norm_pos_iff.1 (hc.trans_le (hcK x hx))
  rw [eLpNorm_congr_ae ((ae_restrict_mem hK).mono fun x hx ↦
    (eq_inv_smul_iff₀ (pow_ne_zero j (hgK x hx))).2
      (conjWirtingerDeriv_pow_mul_add_add_esymm_erase_eq_pow_smul (hg x hx) (hgK x hx) (hb x hx)
        hj (ν x) (μ x) (R x)).symm)]
  refine ContinuousOn.eLpNorm_smul_restrict_le_of_norm_le (φ := fun x ↦ (g x ^ j)⁻¹)
    (ContinuousOn.inv₀ (fun x hx ↦ ((hg x hx).continuousAt.pow j).continuousWithinAt)
      fun x hx ↦ pow_ne_zero j (hgK x hx)) hK (fun x hx ↦ ?_) _ p ρ
  rw [norm_inv, norm_pow]
  exact inv_anti₀ (pow_pos hc j) (pow_le_pow_left₀ hc.le (hcK x hx) j)

end Frame

end TauCeti
