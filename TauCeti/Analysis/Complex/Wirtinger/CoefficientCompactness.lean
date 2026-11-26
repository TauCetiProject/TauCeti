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
import TauCeti.Analysis.Complex.Wirtinger.Precompact
import TauCeti.Analysis.Polynomial.Monic.RootBound
import TauCeti.Order.Filter.AtTopBot
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp
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
as input, there for `C¹` coefficients solving it classically; the regularity of the limits that
this requires is not treated here. The zeroth-order term `∑_{V ∈ R} \bar V e_{j-1}(R ∖ V)` is
a continuous function of the unordered tuple `R ∈ Sym ℂ m`
(`TauCeti.continuous_sum_map_conj_mul_esymm_erase`), hence of the coefficients, through the
elementary symmetric chart `Sym.coeffHomeomorph`; so it converges
locally uniformly with them (`TauCeti.tendstoLocallyUniformlyOn_sum_map_conj_mul_esymm_erase`).
The classical derivatives `\bar∂ b_j` then converge in `L¹` on compact sets to the zeroth-order
term of the limit, and the weak equation passes to the limit
(`TauCeti.hasWeakConjWirtingerDerivOn_of_tendsto_setLIntegral_enorm_sub`). Together with the
compactness above, a subsequence of the coefficients converges to Hölder continuous solutions of
the limiting equation (`TauCeti.exists_strictMono_hasWeakConjWirtingerDerivOn_of_esymm`).

## Main results

* `TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_of_esymm`: locally uniform convergence of
  a subsequence of the coefficients, with Hölder continuous limits of exponent `1 - 2 / p`.
* `TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_of_esymm_of_eq`: the same for
  `p = 2 + 2 / m`, with Hölder exponent `1 / (m + 1)`.
* `TauCeti.continuous_sum_map_conj_mul_esymm_erase`: the zeroth-order term of the equation is
  continuous on `Sym ℂ m`.
* `TauCeti.continuousOn_sum_map_conj_mul_esymm_erase`,
  `TauCeti.tendstoLocallyUniformlyOn_sum_map_conj_mul_esymm_erase`: it is continuous in, and
  converges locally uniformly with, the elementary symmetric functions.
* `TauCeti.exists_hasWeakConjWirtingerDerivOn_of_tendstoLocallyUniformlyOn_esymm`: locally
  uniform limits of the coefficients solve the limiting equation weakly.
* `TauCeti.exists_strictMono_hasWeakConjWirtingerDerivOn_of_esymm`: a subsequence converges to
  Hölder continuous weak solutions of the limiting equation.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open scoped ENNReal NNReal ContDiff ComplexConjugate Topology
open MeasureTheory Set Filter

namespace TauCeti

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
  -- The elementary symmetric functions of submultisets of `R` are bounded by the roots.
  have hE : ∀ S : Multiset ℂ, Multiset.card S ≤ m → (∀ w ∈ S, ‖w‖ ≤ ρ) → ∀ k,
      ‖S.esymm k‖ ≤ m.choose k * ρ ^ k := fun S hS hSρ k ↦
    (Multiset.norm_esymm_le hSρ k).trans (by gcongr)
  have hsum : ‖(R.map fun w ↦ conj w * (R.erase w).esymm (j - 1)).sum‖ ≤
      m * ρ * (m.choose (j - 1) * ρ ^ (j - 1)) := by
    refine (norm_multiset_sum_le _).trans ?_
    rw [Multiset.map_map]
    refine (Multiset.sum_le_card_nsmul _ ((ρ : ℝ) * (m.choose (j - 1) * ρ ^ (j - 1)))
      fun r hr ↦ ?_).trans ?_
    · obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hr
      rw [Function.comp_apply, norm_mul, Complex.norm_conj]
      exact mul_le_mul (hρ w hw) (hE _ (Multiset.card_erase_le.trans hcard)
        (fun v hv ↦ hρ v (Multiset.mem_of_mem_erase hv)) _) (norm_nonneg _) ρ.coe_nonneg
    · rw [Multiset.card_map, nsmul_eq_mul, mul_assoc]
      gcongr
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
          exact hE R hcard hρ j
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

/-- An `m`-element multiset is recovered from its elementary symmetric functions by the inverse
of the elementary symmetric chart. -/
private theorem coeffHomeomorph_symm_esymm {m : ℕ} {R : Multiset ℂ}
    (hR : Multiset.card R = m) :
    (Sym.coeffHomeomorph ℂ m).symm (fun i : Fin m ↦ (-1) ^ (m - (i : ℕ)) * R.esymm (m - i)) =
      Sym.mk R hR := by
  rw [Homeomorph.symm_apply_eq, Sym.coeffHomeomorph_apply]
  funext i
  exact (Sym.coeffEquiv_apply (K := ℂ) (Sym.mk R hR) i).symm

/-- Every tuple of coefficients `c₁, …, c_m` is the tuple of elementary symmetric functions of the
`m` roots of `Wᵐ - c₁ Wᵐ⁻¹ + ⋯ + (-1)ᵐ cₘ`. -/
private theorem exists_card_eq_and_esymm_eq (m : ℕ) (c : ℕ → ℂ) :
    ∃ R : Multiset ℂ, Multiset.card R = m ∧ ∀ j ∈ Finset.Icc 1 m, c j = R.esymm j := by
  set γ : Fin m → ℂ := fun i ↦ (-1) ^ (m - (i : ℕ)) * c (m - i) with hγ
  refine ⟨((Sym.coeffEquiv ℂ m).symm γ : Multiset ℂ), Sym.card_coe, fun j hj ↦ ?_⟩
  obtain ⟨hj₁, hjm⟩ := Finset.mem_Icc.1 hj
  have hi := congrFun ((Sym.coeffEquiv ℂ m).apply_symm_apply γ) ⟨m - j, by omega⟩
  rw [Sym.coeffEquiv_apply] at hi
  simp only [hγ, Nat.sub_sub_self hjm] at hi
  exact (mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hi).symm

/-- **The zeroth-order term depends continuously on the coefficients.** If `R₀ z` has `m` elements
for `z ∈ U` and its elementary symmetric functions `e_j(R₀ z)`, `1 ≤ j ≤ m`, are continuous on
`U`, then so is `z ↦ ∑_{w ∈ R₀ z} \bar w e_k(R₀ z ∖ w)`. -/
theorem continuousOn_sum_map_conj_mul_esymm_erase {m k : ℕ} {U : Set ℂ} {R₀ : ℂ → Multiset ℂ}
    (hcard : ∀ z ∈ U, Multiset.card (R₀ z) = m)
    (hR₀ : ∀ j ∈ Finset.Icc 1 m, ContinuousOn (fun z ↦ (R₀ z).esymm j) U) :
    ContinuousOn (fun z ↦ ((R₀ z).map fun w ↦ conj w * ((R₀ z).erase w).esymm k).sum) U := by
  have hγ : ContinuousOn
      (fun z (i : Fin m) ↦ (-1) ^ (m - (i : ℕ)) * (R₀ z).esymm (m - i)) U :=
    continuousOn_pi.2 fun i ↦ continuousOn_const.mul
      (hR₀ _ (Finset.mem_Icc.2 ⟨by omega, by omega⟩))
  refine ((continuous_sum_map_conj_mul_esymm_erase m k).comp_continuousOn
    ((Sym.coeffHomeomorph ℂ m).symm.continuous.comp_continuousOn hγ)).congr fun z hz ↦ ?_
  simp only [Function.comp_apply, coeffHomeomorph_symm_esymm (hcard z hz), Sym.coe_mk]

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
  set β : ι → ℂ → Fin m → ℂ := fun n z i ↦ (-1) ^ (m - (i : ℕ)) * (R n z).esymm (m - i)
  set γ : ℂ → Fin m → ℂ := fun z i ↦ (-1) ^ (m - (i : ℕ)) * (R₀ z).esymm (m - i)
  set Φ : (Fin m → ℂ) → ℂ := fun v ↦ (((Sym.coeffHomeomorph ℂ m).symm v : Multiset ℂ).map
    fun w ↦ conj w * (((Sym.coeffHomeomorph ℂ m).symm v : Multiset ℂ).erase w).esymm k).sum
  have hΦ : Continuous Φ := (continuous_sum_map_conj_mul_esymm_erase m k).comp
    (Sym.coeffHomeomorph ℂ m).symm.continuous
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).2 fun K hKU hK ↦ ?_
  have hβ : TendstoUniformlyOn β γ l K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Filter.eventually_all.2 fun i : Fin m ↦ Metric.tendstoUniformlyOn_iff.1
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 (hR _ (hmem i)) K hKU hK) ε hε]
      with n hn z hz
    refine (dist_pi_lt_iff hε).2 fun i ↦ ?_
    simpa [β, γ, dist_eq_norm, ← mul_sub, norm_mul, norm_pow] using hn i z hz
  have hγ : ContinuousOn γ K :=
    continuousOn_pi.2 fun i ↦ continuousOn_const.mul ((hR₀ _ (hmem i)).mono hKU)
  refine ((hK.image_of_continuousOn hγ).comp_tendstoUniformlyOn
    (fun _ _ ↦ hΦ.continuousAt) hβ).congr (.of_forall fun n z hz ↦ ?_) |>.congr_right
      fun z hz ↦ ?_
  · simp only [Φ, β, coeffHomeomorph_symm_esymm (hcard n z (hKU hz)), Sym.coe_mk]
  · simp only [Φ, γ, coeffHomeomorph_symm_esymm (hcard₀ z (hKU hz)), Sym.coe_mk]

/-- If `‖F n z - f z‖ ≤ ‖r n z‖ + ‖G n z - g z‖` on a compact set `K`, where `G n → g` uniformly
on `K` and `r n → 0` in `L¹(K)`, then `F n → f` in `L¹(K)`. No measurability is needed: the
uniform part is bounded by a constant. -/
private theorem tendsto_setLIntegral_enorm_sub_of_le {ι : Type*} {l : Filter ι} {K : Set ℂ}
    (hK : IsCompact K) {F G r : ι → ℂ → ℂ} {f g : ℂ → ℂ} (hG : TendstoUniformlyOn G g l K)
    (hr : Tendsto (fun n ↦ ∫⁻ z in K, ‖r n z‖ₑ) l (𝓝 0))
    (hle : ∀ n, ∀ z ∈ K, ‖F n z - f z‖ ≤ ‖r n z‖ + ‖G n z - g z‖) :
    Tendsto (fun n ↦ ∫⁻ z in K, ‖F n z - f z‖ₑ) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  -- Choose `ε > 0` with `ε vol(K) < δ / 2`.
  have hsmall : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal ε * volume K) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal ε) (𝓝[>] 0) (𝓝 0) := by
      simpa using (ENNReal.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using ENNReal.Tendsto.mul_const h0 (Or.inr (hK.measure_lt_top (μ := volume)).ne)
  obtain ⟨ε, hεδ, hε⟩ :=
    ((hsmall.eventually (gt_mem_nhds hδ2)).and self_mem_nhdsWithin).exists
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hG ε hε, ENNReal.tendsto_nhds_zero.1 hr _ hδ2]
    with n hn hrn
  calc ∫⁻ z in K, ‖F n z - f z‖ₑ ≤ ∫⁻ z in K, (‖r n z‖ₑ + ENNReal.ofReal ε) := by
        refine lintegral_mono_ae ((ae_restrict_iff' hK.measurableSet).2
          (.of_forall fun z hz ↦ ?_))
        have hGz : ‖G n z - g z‖ ≤ ε := by
          simpa only [dist_eq_norm, norm_sub_rev] using (hn z hz).le
        rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_add (norm_nonneg _) (le_of_lt hε)]
        exact ENNReal.ofReal_le_ofReal ((hle n z hz).trans (by gcongr))
    _ = (∫⁻ z in K, ‖r n z‖ₑ) + ENNReal.ofReal ε * volume K := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    _ ≤ δ / 2 + δ / 2 := add_le_add hrn hεδ.le
    _ = δ := ENNReal.add_halves δ

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
  choose R₀ hcard₀ hcR₀ using fun z ↦ exists_card_eq_and_esymm_eq m fun j ↦ c j z
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
  have hev : LipschitzWith 1 fun L : ℂ →L⋆[ℂ] ℂ ↦ L 1 :=
    LipschitzWith.of_dist_le_mul fun L L' ↦ by simpa [dist_eq_norm] using (L - L').le_opNorm 1
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
    (fun K hKU hK ↦ tendsto_setLIntegral_enorm_sub_of_le (r := 0) hK (hloc K hKU hK (hc j hj))
      (by simp) fun n z _ ↦ by simp) fun K hKU hK ↦ ?_
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
  refine tendsto_setLIntegral_enorm_sub_of_le hK hA (hr K hKU hK j hj) fun n z _ ↦
    le_of_eq_of_le (congrArg norm ?_) (norm_sub_le _ _)
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

end TauCeti
