/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Compactness
public import TauCeti.Analysis.Complex.Wirtinger.Weak
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Analysis.Complex.Wirtinger.Precompact
import TauCeti.Analysis.Polynomial.SymmetricPower
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp
import TauCeti.Analysis.Polynomial.Monic.RootBound
import TauCeti.Order.Filter.AtTopBot
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Compactness of coefficients solving the equation of elementary symmetric functions

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

If moreover the remainders tend to `0` in `L¹` on each compact subset of `U`, and the forms `ν`,
`μ` converge locally uniformly, then the limits `c_j` of the coefficients solve the equation with
zero remainder, in the sense of distributions: they are the elementary symmetric functions of the
roots `R₀(z)` of `Wᵐ - c₁(z) W^(m-1) + ⋯ + (-1)ᵐ c_m(z)`, and
`\bar∂ c_j + j ν c_j + μ ∑_{V ∈ R₀} \bar V e_{j-1}(R₀ ∖ V) = 0`
(`TauCeti.hasWeakConjWirtingerDerivOn_of_tendstoLocallyUniformlyOn_esymm`). The zeroth-order term
is a continuous function of the coefficients, because the roots of a monic polynomial depend
continuously on its coefficients (`Sym.coeffHomeomorph`) and the term is a polynomial in the
elementary symmetric functions of the roots and the sums `∑_{V ∈ R} Vᵏ \bar V`
(`Multiset.sum_map_mul_esymm_erase`). So the zeroth-order terms converge locally uniformly along
with the coefficients, and the weak equation passes to the limit
(`TauCeti.HasWeakConjWirtingerDerivOn.of_tendsto_setLIntegral_enorm_sub`). This is the coefficient
equation that `TauCeti.Analysis.Complex.Wirtinger.Root.Collision` and
`TauCeti.Analysis.Complex.Wirtinger.Root.Normalization` start from; there the coefficients are
assumed `C¹`, which the weak equation alone does not give.

## Main results

* `TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_of_esymm`: locally uniform convergence of
  a subsequence of the coefficients, with Hölder continuous limits of exponent `1 - 2 / p`.
* `TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_of_esymm_of_eq`: the same for
  `p = 2 + 2 / m`, with Hölder exponent `1 / (m + 1)`.
* `TauCeti.hasWeakConjWirtingerDerivOn_of_tendstoLocallyUniformlyOn_esymm`: when the remainders
  tend to `0`, the limits solve the equation of the elementary symmetric functions weakly.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open scoped ENNReal NNReal ContDiff ComplexConjugate Topology
open MeasureTheory Set Filter TopologicalSpace

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

/-! ### The limits solve the equation -/

/-- The unordered `m`-tuple whose elementary symmetric functions `e₁, …, e_m` are
`d 0, …, d (m - 1)`: the roots of `Wᵐ - d 0 W^(m-1) + d 1 W^(m-2) - ⋯`, read through the
elementary symmetric chart. -/
private noncomputable def tupleOfEsymm {m : ℕ} (d : Fin m → ℂ) : Sym ℂ m :=
  (Sym.coeffHomeomorph ℂ m).symm fun i ↦ (-1) ^ (m - (i : ℕ)) * d (Fin.rev i)

private theorem continuous_tupleOfEsymm {m : ℕ} : Continuous (tupleOfEsymm (m := m)) :=
  (Sym.coeffHomeomorph ℂ m).symm.continuous.comp <| continuous_pi fun _ ↦
    continuous_const.mul (continuous_apply _)

private theorem esymm_tupleOfEsymm {m : ℕ} (d : Fin m → ℂ) (i : Fin m) :
    ((tupleOfEsymm d : Sym ℂ m) : Multiset ℂ).esymm (i + 1) = d i := by
  have h := congrFun ((Sym.coeffHomeomorph ℂ m).apply_symm_apply
    fun i ↦ (-1) ^ (m - (i : ℕ)) * d (Fin.rev i)) (Fin.rev i)
  rw [Sym.coeffHomeomorph_apply, Sym.coeffEquiv_apply, Fin.rev_rev, Fin.val_rev,
    show m - (m - (i + 1)) = i + 1 by omega] at h
  exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) h

private theorem coe_tupleOfEsymm {m : ℕ} {S : Multiset ℂ} (hS : Multiset.card S = m)
    {d : Fin m → ℂ} (hd : ∀ i : Fin m, S.esymm (i + 1) = d i) :
    ((tupleOfEsymm d : Sym ℂ m) : Multiset ℂ) = S := by
  suffices h : tupleOfEsymm d = Sym.mk S hS by rw [h]; rfl
  rw [tupleOfEsymm, Homeomorph.symm_apply_eq]
  funext i
  rw [Sym.coeffHomeomorph_apply, Sym.coeffEquiv_apply, ← hd, Fin.val_rev,
    show m - (i + 1) + 1 = m - i by omega]
  rfl

private theorem esymm_tupleOfEsymm_of_mem {m j : ℕ} (hj : j ∈ Finset.Icc 1 m) (e : ℕ → ℂ) :
    ((tupleOfEsymm (fun i : Fin m ↦ e (i + 1)) : Sym ℂ m) : Multiset ℂ).esymm j = e j := by
  obtain ⟨hj1, hjm⟩ := Finset.mem_Icc.1 hj
  obtain ⟨i, rfl⟩ : ∃ i : Fin m, (i : ℕ) + 1 = j := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  exact esymm_tupleOfEsymm _ i

/-- The zeroth-order term `∑_{V ∈ s} \bar V e_{j-1}(s ∖ V)` of the equation of the elementary
symmetric functions is continuous on the symmetric power: by `Multiset.sum_map_mul_esymm_erase`
it is a polynomial in the elementary symmetric functions of `s` and the sums
`∑_{V ∈ s} Vᵏ \bar V`. -/
private theorem continuous_sum_map_conj_mul_esymm_erase (m j : ℕ) :
    Continuous fun s : Sym ℂ m ↦
      ((s : Multiset ℂ).map fun w ↦ conj w * ((s : Multiset ℂ).erase w).esymm (j - 1)).sum := by
  simp_rw [Multiset.sum_map_mul_esymm_erase]
  exact continuous_finsetSum _ fun k _ ↦ (continuous_const.mul (Sym.continuous_esymm _)).mul
    (Sym.continuous_sum_map ((continuous_pow k).mul Complex.continuous_conj))

/-- The zeroth-order term `(j e_j ν + ∑_{V ∈ R} \bar V e_{j-1}(R ∖ V) μ)(1)` of the equation of
the `j`-th elementary symmetric function, as a function of the coefficients `e₁, …, e_m` of the
tuple `R` (`tupleOfEsymm`) and of the forms `ν`, `μ`. -/
private noncomputable def esymmZerothOrder (m j : ℕ)
    (p : (Fin m → ℂ) × (ℂ →L⋆[ℂ] ℂ) × (ℂ →L⋆[ℂ] ℂ)) : ℂ :=
  ((j * ((tupleOfEsymm p.1 : Sym ℂ m) : Multiset ℂ).esymm j) • p.2.1 +
    (((tupleOfEsymm p.1 : Sym ℂ m) : Multiset ℂ).map fun w ↦
      conj w * (((tupleOfEsymm p.1 : Sym ℂ m) : Multiset ℂ).erase w).esymm (j - 1)).sum • p.2.2) 1

private theorem continuous_esymmZerothOrder (m j : ℕ) : Continuous (esymmZerothOrder m j) := by
  have h₁ := (Sym.continuous_esymm (R := ℂ) (n := m) j).comp continuous_tupleOfEsymm
  have h₂ := (continuous_sum_map_conj_mul_esymm_erase m j).comp continuous_tupleOfEsymm
  exact (continuous_eval_const 1).comp
    (((continuous_const.mul (h₁.comp continuous_fst)).smul (continuous_fst.comp continuous_snd)).add
      ((h₂.comp continuous_fst).smul (continuous_snd.comp continuous_snd)))

/-- **The limits of the coefficients solve the equation of elementary symmetric functions.**
Let `U ⊆ ℂ` be open. For each `n` let `R n z` be a multiset of `m` complex numbers, for `z ∈ U`,
let `b n j` be `C¹` on `U` and equal to the `j`-th elementary symmetric function of `R n z` there,
for `1 ≤ j ≤ m`, and let `ν n`, `μ n` be `(0,1)`-forms continuous on `U`, converging locally
uniformly on `U` to `ν₀`, `μ₀`. Suppose that the coefficients `b n j` converge locally uniformly on
`U` to `c j`, and that the remainders

`r_j = \bar∂ b_j + j ν b_j + μ ∑_{V ∈ R} \bar V e_{j-1}(R ∖ V)`

tend to `0` in `L¹` on each compact subset of `U`. Then `c₁, …, c_m` are the elementary symmetric
functions of multisets `R₀ z` of `m` points, the roots of `Wᵐ - c₁(z) W^(m-1) + ⋯ + (-1)ᵐ c_m(z)`,
and they solve the equation with zero remainder in the sense of distributions on `U`:

`\bar∂ c_j + j ν₀ c_j + μ₀ ∑_{V ∈ R₀} \bar V e_{j-1}(R₀ ∖ V) = 0`.

The zeroth-order terms converge locally uniformly, by continuity of the roots of a monic polynomial
in its coefficients (`Sym.coeffHomeomorph`), and the weak equation passes to the limit
(`TauCeti.HasWeakConjWirtingerDerivOn.of_tendsto_setLIntegral_enorm_sub`). -/
theorem hasWeakConjWirtingerDerivOn_of_tendstoLocallyUniformlyOn_esymm {m : ℕ} {U : Opens ℂ}
    {b : ℕ → ℕ → ℂ → ℂ} {R : ℕ → ℂ → Multiset ℂ} {ν μ : ℕ → ℂ → ℂ →L⋆[ℂ] ℂ}
    {c : ℕ → ℂ → ℂ} {ν₀ μ₀ : ℂ → ℂ →L⋆[ℂ] ℂ}
    (hb : ∀ n, ∀ j ∈ Finset.Icc 1 m, ContDiffOn ℝ 1 (b n j) U)
    (hcard : ∀ n, ∀ z ∈ U, Multiset.card (R n z) = m)
    (hbR : ∀ n, ∀ j ∈ Finset.Icc 1 m, ∀ z ∈ U, b n j z = (R n z).esymm j)
    (hν : ∀ n, ContinuousOn (ν n) U) (hμ : ∀ n, ContinuousOn (μ n) U)
    (hν₀ : TendstoLocallyUniformlyOn ν ν₀ atTop U) (hμ₀ : TendstoLocallyUniformlyOn μ μ₀ atTop U)
    (hc : ∀ j ∈ Finset.Icc 1 m, TendstoLocallyUniformlyOn (fun n ↦ b n j) (c j) atTop U)
    (hr : ∀ K ⊆ (U : Set ℂ), IsCompact K → ∀ j ∈ Finset.Icc 1 m,
      Tendsto (fun n ↦ ∫⁻ z in K, ‖(conjWirtingerDeriv (b n j) z + (j * b n j z) • ν n z +
        ((R n z).map fun w ↦ conj w * ((R n z).erase w).esymm (j - 1)).sum • μ n z) 1‖ₑ)
          atTop (𝓝 0)) :
    ∃ R₀ : ℂ → Multiset ℂ, (∀ z ∈ U, Multiset.card (R₀ z) = m) ∧
      (∀ j ∈ Finset.Icc 1 m, ∀ z ∈ U, c j z = (R₀ z).esymm j) ∧
      ∀ j ∈ Finset.Icc 1 m, HasWeakConjWirtingerDerivOn volume U (c j) fun z ↦
        -((j * c j z) • ν₀ z +
          ((R₀ z).map fun w ↦ conj w * ((R₀ z).erase w).esymm (j - 1)).sum • μ₀ z) 1 := by
  -- The coefficient tuples `(e₁, …, e_m)` along the sequence and in the limit.
  set D : ℕ → ℂ → Fin m → ℂ := fun n z i ↦ b n (i + 1) z
  set D₀ : ℂ → Fin m → ℂ := fun z i ↦ c (i + 1) z
  have hmem (i : Fin m) : (i : ℕ) + 1 ∈ Finset.Icc 1 m := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hD₀U : ContinuousOn D₀ U := continuousOn_pi.2 fun i ↦ (hc _ (hmem i)).continuousOn
    (Frequently.of_forall fun n ↦ (hb n _ (hmem i)).continuousOn)
  have hF₀U : ContinuousOn (fun z ↦ (D₀ z, ν₀ z, μ₀ z)) U := hD₀U.prodMk
    ((hν₀.continuousOn (Frequently.of_forall hν)).prodMk
      (hμ₀.continuousOn (Frequently.of_forall hμ)))
  -- Along the sequence, the tuple of `D n z` is `R n z`.
  have hR (n : ℕ) (z : ℂ) (hz : z ∈ U) : ((tupleOfEsymm (D n z) : Sym ℂ m) : Multiset ℂ) = R n z :=
    coe_tupleOfEsymm (hcard n z hz) fun i ↦ (hbR n _ (hmem i) z hz).symm
  refine ⟨fun z ↦ tupleOfEsymm (D₀ z), fun z _ ↦ (tupleOfEsymm (D₀ z)).card_coe,
    fun j hj z _ ↦ (esymm_tupleOfEsymm_of_mem hj (c · z)).symm, fun j hj ↦ ?_⟩
  -- The limiting zeroth-order term is that of the limiting coefficients and forms.
  have htarget : (fun z ↦ -((j * c j z) • ν₀ z +
      (((tupleOfEsymm (D₀ z) : Sym ℂ m) : Multiset ℂ).map fun w ↦
        conj w * (((tupleOfEsymm (D₀ z) : Sym ℂ m) : Multiset ℂ).erase w).esymm (j - 1)).sum •
          μ₀ z) 1) = fun z ↦ -esymmZerothOrder m j (D₀ z, ν₀ z, μ₀ z) := by
    funext z
    have he : ((tupleOfEsymm (D₀ z) : Sym ℂ m) : Multiset ℂ).esymm j = c j z :=
      esymm_tupleOfEsymm_of_mem hj (c · z)
    simp only [esymmZerothOrder, he]
  rw [htarget]
  refine hasWeakConjWirtingerDerivOn_of_tendstoLocallyUniformlyOn (hb · j hj) (hc j hj)
    (g := fun n z ↦ -esymmZerothOrder m j (D n z, ν n z, μ n z))
    (fun n ↦ ((continuous_esymmZerothOrder m j).comp_continuousOn
      ((continuousOn_pi.2 fun i ↦ (hb n _ (hmem i)).continuousOn : ContinuousOn (D n) U).prodMk
        ((hν n).prodMk (hμ n)))).neg) ?_ fun K hKU hK ↦ ?_
  · -- The zeroth-order terms converge locally uniformly, being continuous in the coefficients.
    refine TendstoLocallyUniformlyOn.neg ?_
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact U.isOpen]
    intro K hKU hK
    exact (hK.image_of_continuousOn (hF₀U.mono hKU)).comp_tendstoUniformlyOn
      (fun _ _ ↦ (continuous_esymmZerothOrder m j).continuousAt)
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact U.isOpen).1
        ((tendstoLocallyUniformlyOn_pi fun i ↦ hc _ (hmem i)).prodMk (hν₀.prodMk hμ₀)) K hKU hK)
  · -- On `U`, `\bar∂ b_j` plus the zeroth-order term is the remainder.
    refine (hr K hKU hK j hj).congr fun n ↦ setLIntegral_congr_fun hK.measurableSet fun z hz ↦ ?_
    simp only [esymmZerothOrder, hR n z (hKU hz), ← hbR n j hj z (hKU hz), add_apply,
      sub_neg_eq_add, add_assoc]

end TauCeti
