/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.ChangeOfVariables
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Basic
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.Calculus.IteratedFDeriv.OrthonormalBasis
import TauCeti.Analysis.Distribution.SchwartzSpace.ChangeOfVariables
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TemperedDistribution.Bernstein
import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.AlmostDiagonal
import TauCeti.MeasureTheory.Function.Jacobian

/-!
# Pullback by a diffeomorphism on Besov spaces

Let `Φ : E ≃ E` be a bijection such that `Φ` and `Φ⁻¹` have temperate growth and bounded
derivatives of positive order, say of orders `1` to `N + 1` with `N > |s|`. Pulling tempered
distributions back along `Φ` (`TemperedDistribution.compCLM`) maps every inhomogeneous Besov space
`B^s_{p,q}`, `1 ≤ p, q ≤ ∞`, boundedly to itself
(`TauCeti.BesovSpace.exists_toDistr_eq_compCLM_and_norm_le`), with an operator norm depending only
on the bump function `φ`, on `s`, `N` and the derivative bounds, and not on `p` or `q`. Pulling back
along `Φ⁻¹` inverts it, so it is an isomorphism of `B^s_{p,q}` (`TauCeti.BesovSpace.compCLE`). This
covers the Hölder–Zygmund scale `𝒞^s = B^s_{∞,∞}` and negative orders `s < 0`. Together with
smooth multipliers (`TauCeti.BesovSpace.smulLeftCLM`), these give the changes of coordinates and
the scalar case of the matrix-valued changes of frame needed to define Besov norms of sections of
vector bundles by finite atlases.

The proof shows that `Φ^*` is almost diagonal for the Littlewood–Paley blocks: for every `M ≤ N`,

`‖Δⱼ (Φ^* Δₖ u)‖_p ≤ K 2^{-M |j - k|} ‖Δₖ u‖_p`

(`TauCeti.exists_littlewoodPaleyBlock_compCLM_eq_and_norm_le`), and then applies
`TauCeti.BesovSpace.exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_le`. The Jacobian of `Φ`
is bounded below in terms of the derivative of `Φ⁻¹`, so `Φ^*` is bounded on `Lᵖ` uniformly in `p`
(`TemperedDistribution.exists_compCLM_toTemperedDistribution_eq_and_norm_le`).

* For `j > k`, the spectrum of `Δⱼ Φ^* f`, `f = Δₖ u`, lies in the `j`-th dyadic annulus, where the
  reverse Bernstein inequality bounds a function by `2^{-jM}` times its derivatives of order `M`. By
  the chain rule `∂_v (Φ^* f) = ∑ᵢ cᵢ Φ^* (∂_{bᵢ} f)` (`TemperedDistribution.lineDerivOp_compCLM`),
  with coefficients `DΦ(x) v = ∑ᵢ cᵢ(x) bᵢ` bounded with their derivatives, and Bernstein's
  inequality for `f`, those derivatives are `O(2^{kM})`.
* For `j < k`, the block `f` lies in the `k`-th annulus, so `f = ∑ᵢ ∂_{bᵢ} hᵢ` with
  `‖hᵢ‖_p = O(2^{-k} ‖f‖_p)`. By the chain rule for `Φ⁻¹`,
  `Φ^* (∂_{bᵢ} hᵢ) = ∑ₗ dᵢₗ ∂_{bₗ} (Φ^* hᵢ)` (`TemperedDistribution.compCLM_lineDerivOp`), and
  `dᵢₗ ∂_{bₗ} Y = ∂_{bₗ} (dᵢₗ Y) - (∂_{bₗ} dᵢₗ) Y` moves the derivative onto `Δⱼ`, where it costs
  `2^j`. Repeating this `M` times, with products of such coefficients, gains `2^{M (j - k)}`.
* For `j = k` the pullback and the block are bounded on `Lᵖ`.

## Main declarations

* `TauCeti.exists_littlewoodPaleyBlock_compCLM_eq_and_norm_le`: the block estimate above, the case
  `g = 1` of the estimate `TauCeti.exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le`
  for `Δⱼ (g Φ^* Δₖ u)`, whose case `Φ = id` gives the one for smooth multipliers.
* `TauCeti.BesovSpace.exists_toDistr_eq_compCLM_and_norm_le`: `Φ^*` maps `B^s_{p,q}` to itself with
  norm at most a constant depending only on `φ`, `s`, `N` and the derivative bounds.
* `TemperedDistribution.MemBesov.compCLM`: `B^s_{p,q}` is stable under pullback along `Φ`.
* `TemperedDistribution.memBesov_compCLM_iff`: `u ∈ B^s_{p,q}` if and only if `Φ^* u ∈ B^s_{p,q}`.
* `TauCeti.BesovSpace.compCLE`: the pullback as an isomorphism of `B^s_{p,q}`, with inverse the
  pullback along `Φ⁻¹` (`TauCeti.BesovSpace.compCLE_symm`), contravariantly functorial
  (`TauCeti.BesovSpace.compCLE_refl`, `TauCeti.BesovSpace.compCLE_trans`), and with norm bounded
  uniformly in `p` and `q` (`TauCeti.BesovSpace.exists_norm_compCLE_le`).
* `TauCeti.BesovSpace.compCLM`: the pullback as a bounded operator on `B^s_{p,q}` under the weaker
  derivative bounds of `TemperedDistribution.MemBesov.compCLM`, with norm bounded uniformly in `p`
  and `q` (`TauCeti.BesovSpace.exists_norm_compCLM_le`).
* `TauCeti.BesovSpace.compCLEOfContDiff`: the isomorphism for a smooth diffeomorphism with bounded
  derivatives of every positive order.
* `TauCeti.BesovSpace.translateEquiv`, `TauCeti.BesovSpace.compContinuousLinearEquiv`: translations,
  with norms bounded uniformly in the translation
  (`TauCeti.BesovSpace.exists_norm_translateEquiv_le`), and continuous linear automorphisms of `E`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Springer, 1976, §6.4.
* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §2.10.2 (diffeomorphisms of `ℝⁿ` on
  Besov spaces).
-/

public section

noncomputable section

open MeasureTheory Metric Distribution FourierTransform
open scoped ENNReal SchwartzMap LineDeriv ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti

open TemperedDistribution

omit [MeasurableSpace E] [BorelSpace E] in
private theorem norm_iteratedFDeriv_repr_fderiv_comp_le {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {Φ Ψ : E → E} (hΦ : ContDiff ℝ ∞ Φ) (hΨ : ContDiff ℝ ∞ Ψ) {M : ℕ}
    {L : ℝ} (hΦL : ∀ n, 1 ≤ n → n ≤ M → ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ L)
    (hΨL : ∀ n, 1 ≤ n → n ≤ M + 1 → ∀ x, ‖iteratedFDeriv ℝ n Ψ x‖ ≤ L) (v : E) (i : ι) :
    ∀ n ≤ M, ∀ x, ‖iteratedFDeriv ℝ n
      (fun x ↦ ((b.toBasis.repr (fderiv ℝ Ψ (Φ x) v) i : ℝ) : ℂ)) x‖ ≤
        M.factorial * (L * ‖v‖) * max 1 L ^ M := by
  intro n hn x
  have hd : ContDiff ℝ ∞ (fun y ↦ ((b.toBasis.repr (fderiv ℝ Ψ y v) i : ℝ) : ℂ)) := by
    have : ContDiff ℝ ∞ (fun y ↦ fderiv ℝ Ψ y v) :=
      (hΨ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    exact (Complex.ofRealCLM.contDiff.comp
      ((b.toBasis.coord i).toContinuousLinearMap.contDiff)).comp this
  have hc (n : ℕ) (hn : n ≤ M) (y : E) :
      ‖iteratedFDeriv ℝ n (fun x ↦ ((b.toBasis.repr (fderiv ℝ Ψ x v) i : ℝ) : ℂ)) y‖ ≤ L * ‖v‖ :=
    (hΨ.norm_iteratedFDeriv_basis_repr_fderiv_apply_le (mod_cast le_top) b v i y).trans
      (mul_le_mul_of_nonneg_right (hΨL (n + 1) (by omega) (by omega) y) (norm_nonneg v))
  have hL0 : 0 ≤ L * ‖v‖ := (norm_nonneg _).trans (hc 0 (Nat.zero_le _) x)
  refine (norm_iteratedFDeriv_comp_le (g := fun y ↦ ((b.toBasis.repr (fderiv ℝ Ψ y v) i : ℝ) : ℂ))
    hd hΦ (mod_cast le_top) x (fun k hk ↦ hc k (hk.trans hn) (Φ x))
    (fun k hk₁ hk₂ ↦ ((hΦL k hk₁ (hk₂.trans hn) x).trans (le_max_right 1 L)).trans
      (le_self_pow₀ (le_max_left 1 L) (by omega)))).trans ?_
  gcongr
  exact le_max_left 1 L

/-- The pullback of an `Lᵖ` function, with the `p`-independent bound `J` for `J⁻¹ ≤ |det DΦ|`. -/
private theorem exists_compCLM_eq_and_norm_le {p : ℝ≥0∞} [Fact (1 ≤ p)] {Φ : E ≃ E}
    (hΦ : (Φ : E → E).HasTemperateGrowth) (hΨ : (Φ.symm : E → E).HasTemperateGrowth) {J : ℝ}
    (hJ : 1 ≤ J) (hdet : ∀ x, J⁻¹ ≤ |(fderiv ℝ Φ x).det|) (f : Lp F p (volume : Measure E)) :
    ∃ v : Lp F p (volume : Measure E), compCLM F Φ hΦ hΨ (f : 𝓢'(E, F)) = v ∧ ‖v‖ ≤ J * ‖f‖ := by
  obtain ⟨v, hv, -, hvn⟩ := exists_compCLM_toTemperedDistribution_eq_and_norm_le volume hΦ hΨ
    (inv_pos.2 (zero_lt_one.trans_le hJ)) hdet f
  refine ⟨v, hv, hvn.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))⟩
  rw [inv_inv]
  have hp : p.toReal⁻¹ ≤ 1 := by
    rcases eq_or_ne p ⊤ with rfl | hp
    · simp
    · exact inv_le_one_of_one_le₀ (by
        simpa using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p))
  simpa using Real.rpow_le_rpow_of_exponent_le hJ hp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The coefficients `cᵢ` of `DΦ(x) w = ∑ᵢ cᵢ(x) bᵢ`, multiplied by a function `g` of temperate
growth, have temperate growth, and the derivatives of `cᵢ g` of order at most `M` are bounded in
terms of those of `Φ` and `g`. -/
private theorem hasTemperateGrowth_and_norm_iteratedFDeriv_repr_fderiv_mul_le {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℝ E) {Φ : E → E} (hΦ : Φ.HasTemperateGrowth) {M : ℕ}
    {L : ℝ} (hΦL : ∀ n, 1 ≤ n → n ≤ M + 1 → ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ L) {g : E → ℂ}
    {G : ℝ} (hg : g.HasTemperateGrowth) (hgG : ∀ n ≤ M, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ G)
    (w : E) (i : ι) :
    ((fun x ↦ ((b.toBasis.repr (fderiv ℝ Φ x w) i : ℝ) : ℂ)) * g).HasTemperateGrowth ∧
      ∀ n ≤ M, ∀ x, ‖iteratedFDeriv ℝ n
        ((fun x ↦ ((b.toBasis.repr (fderiv ℝ Φ x w) i : ℝ) : ℂ)) * g) x‖ ≤
          2 ^ M * (L * ‖w‖ * G) := by
  have hc : (fun x ↦ ((b.toBasis.repr (fderiv ℝ Φ x w) i : ℝ) : ℂ)).HasTemperateGrowth :=
    hΦ.basis_repr_fderiv_apply b.toBasis w i
  exact ⟨hc.mul hg, fun n hn x ↦ (hc.1.of_le (mod_cast le_top)).norm_iteratedFDeriv_mul_le_two_pow
    (hg.1.of_le (mod_cast le_top)) (fun n hn ↦
      (hΦ.1.norm_iteratedFDeriv_basis_repr_fderiv_apply_le (mod_cast le_top) b w i x).trans
        (mul_le_mul_of_nonneg_right (hΦL (n + 1) (by omega) (by omega) x) (norm_nonneg w)))
    (fun n hn ↦ hgG n hn x) n hn⟩

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
/-- One derivative of `g Φ^* T`, by the Leibniz rule and the chain rule:
`∂_w (g Φ^* T) = (∂_w g) Φ^* T + ∑ᵢ cᵢ g Φ^* (∂_{bᵢ} T)`, where `DΦ(x) w = ∑ᵢ cᵢ(x) bᵢ`. -/
private theorem lineDerivOp_smulLeftCLM_compCLM {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {Φ : E ≃ E} (hΦ : (Φ : E → E).HasTemperateGrowth)
    (hΨ : (Φ.symm : E → E).HasTemperateGrowth) {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (T : 𝓢'(E, F)) (w : E) :
    ∂_{w} (smulLeftCLM F g (compCLM F Φ hΦ hΨ T)) =
      smulLeftCLM F (fun x ↦ fderiv ℝ g x w) (compCLM F Φ hΦ hΨ T) +
        ∑ i, smulLeftCLM F ((fun x ↦ ((b.toBasis.repr (fderiv ℝ Φ x w) i : ℝ) : ℂ)) * g)
          (compCLM F Φ hΦ hΨ (∂_{b i} T)) := by
  rw [lineDerivOp_smulLeftCLM hg, lineDerivOp_compCLM b.toBasis hΦ hΨ, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hc : (fun x ↦ ((b.toBasis.repr (fderiv ℝ Φ x w) i : ℝ) : ℂ)).HasTemperateGrowth :=
    hΦ.basis_repr_fderiv_apply b.toBasis w i
  rw [smulLeftCLM_smulLeftCLM_apply hc hg, OrthonormalBasis.coe_toBasis]

/-- The inductive step of `exists_iteratedLineDerivOp_smulLeftCLM_compCLM_eq_and_norm_le`: by the
Leibniz and chain rules, `∂_w (g Φ^* f) = (∂_w g) Φ^* f + ∑ᵢ cᵢ g Φ^* (∂_{bᵢ} f)`, and Bernstein's
inequality bounds `∂_{bᵢ} f` by `R ‖f‖_p`, so a bound for the derivatives of order `M` gives one
for those of order `M + 1`. -/
private theorem exists_iteratedLineDerivOp_smulLeftCLM_compCLM_eq_and_norm_le_succ {J : ℝ}
    (L : ℝ) {M : ℕ}
    (ih :
      ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {Φ : E ≃ E} (hΦ : (Φ : E → E).HasTemperateGrowth)
        (hΨ : (Φ.symm : E → E).HasTemperateGrowth), (∀ x, J⁻¹ ≤ |(fderiv ℝ Φ x).det|) →
        (∀ n, 1 ≤ n → n ≤ M → ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ L) →
        ∀ {g : E → ℂ} {G : ℝ}, g.HasTemperateGrowth →
        (∀ n ≤ M, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ G) → ∀ {R : ℝ}, 0 < R →
        ∀ f : Lp F p (volume : Measure E),
        IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ → ∀ m : Fin M → E,
        ∃ w : Lp F p (volume : Measure E),
          ∂^{m} (smulLeftCLM F g (compCLM F Φ hΦ hΨ (f : 𝓢'(E, F)))) = w ∧
          ‖w‖ ≤ K * G * max 1 R ^ M * (∏ i, ‖m i‖) * ‖f‖) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {Φ : E ≃ E} (hΦ : (Φ : E → E).HasTemperateGrowth)
      (hΨ : (Φ.symm : E → E).HasTemperateGrowth), (∀ x, J⁻¹ ≤ |(fderiv ℝ Φ x).det|) →
      (∀ n, 1 ≤ n → n ≤ M + 1 → ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ L) →
      ∀ {g : E → ℂ} {G : ℝ}, g.HasTemperateGrowth →
      (∀ n ≤ M + 1, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ G) → ∀ {R : ℝ}, 0 < R →
      ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ → ∀ m : Fin (M + 1) → E,
      ∃ w : Lp F p (volume : Measure E),
        ∂^{m} (smulLeftCLM F g (compCLM F Φ hΦ hΨ (f : 𝓢'(E, F)))) = w ∧
        ‖w‖ ≤ K * G * max 1 R ^ (M + 1) * (∏ i, ‖m i‖) * ‖f‖ := by
  set b := stdOrthonormalBasis ℝ E
  obtain ⟨CB, hCB, hB⟩ :=
    exists_lineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier (E := E) (F := F)
  obtain ⟨K, hK, hKb⟩ := ih
  set d := Module.finrank ℝ E
  refine ⟨K * (1 + d * 2 ^ M * max L 0 * CB), by positivity,
    fun {p} _ {Φ} hΦ hΨ hdet hΦL {g G} hg hgG R hR f hf m ↦ ?_⟩
  set w := m (Fin.last M)
  have hG : 0 ≤ G := (nonneg_and_norm_le_of_norm_iteratedFDeriv_le hgG).1
  -- The derivatives `∂_{bᵢ} f` are band-limited to the same ball.
  choose f' hf' hf'n using fun i ↦ hB hR f hf (b i)
  have hf'v (i) : IsVanishingOn (𝓕 (f' i : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ := by
    rw [← hf' i]
    exact isVanishingOn_fourier_lineDerivOp hf _
  -- The products `cᵢ g` with the coefficients of the chain rule, `DΦ(x) w = ∑ᵢ cᵢ(x) bᵢ`.
  have hcg (i) := hasTemperateGrowth_and_norm_iteratedFDeriv_repr_fderiv_mul_le b hΦ (M := M)
    hΦL hg (fun n hn ↦ hgG n (by omega)) w i
  have hΦL' : ∀ n, 1 ≤ n → n ≤ M → ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ L :=
    fun n h₁ h₂ ↦ hΦL n h₁ (by omega)
  obtain ⟨v₁, hv₁, hv₁n⟩ := hKb hΦ hΨ hdet hΦL' (hg.fderiv_apply w)
    (hg.1.norm_iteratedFDeriv_fderiv_apply_le_of_forall_le (by
      rw [minSmoothness_of_isRCLikeNormedField]; exact_mod_cast le_top) hgG w) hR f hf
    (Fin.init m)
  choose v₂ hv₂ hv₂n using fun i ↦ hKb hΦ hΨ hdet hΦL' (hcg i).1 (hcg i).2 hR (f' i)
    (hf'v i) (Fin.init m)
  refine ⟨v₁ + ∑ i, v₂ i, ?_, ?_⟩
  · rw [LineDeriv.iteratedLineDerivOp_succ_right, lineDerivOp_smulLeftCLM_compCLM b hΦ hΨ hg,
      LineDeriv.iteratedLineDerivOp_add, LineDeriv.iteratedLineDerivOp_sum, hv₁,
      Lp.toTemperedDistribution_add, Lp.toTemperedDistribution_sum]
    simp only [w] at hv₂
    simp_rw [hf', hv₂]
  · -- Each `v₂ i` gains `‖∂_{bᵢ} f‖ ≤ CB R ‖f‖` over `v₁`, and `1 + a R ≤ (1 + a) max 1 R`.
    have hL : 0 ≤ L := (norm_nonneg _).trans (hΦL 1 le_rfl (by omega) 0)
    set P := ∏ i, ‖Fin.init m i‖
    have hR₁ : R ≤ max 1 R := le_max_right 1 R
    calc ‖v₁ + ∑ i, v₂ i‖ ≤ ‖v₁‖ + ∑ i, ‖v₂ i‖ :=
          (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
      _ ≤ K * (G * ‖w‖) * max 1 R ^ M * P * ‖f‖ + ∑ _i : Fin d,
          K * (2 ^ M * (L * ‖w‖ * G)) * max 1 R ^ M * P * (CB * R * ‖f‖) := by
        refine add_le_add hv₁n (Finset.sum_le_sum fun i _ ↦ (hv₂n i).trans ?_)
        gcongr
        simpa [b.orthonormal.1 i] using hf'n i
      _ ≤ K * G * ‖w‖ * max 1 R ^ M * P * ‖f‖ * ((1 + d * 2 ^ M * max L 0 * CB) * max 1 R) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, max_eq_left hL]
        have ha : 0 ≤ d * 2 ^ M * L * CB := by positivity
        have : 1 + d * 2 ^ M * L * CB * R ≤ (1 + d * 2 ^ M * L * CB) * max 1 R := by
          nlinarith [le_max_left 1 R]
        calc _ = K * G * ‖w‖ * max 1 R ^ M * P * ‖f‖ * (1 + d * 2 ^ M * L * CB * R) := by ring
          _ ≤ _ := by gcongr
      _ = K * (1 + d * 2 ^ M * max L 0 * CB) * G * max 1 R ^ (M + 1) * (∏ i, ‖m i‖) * ‖f‖ := by
        rw [Fin.prod_univ_castSucc]
        simp only [P, Fin.init, w]
        ring

/-- **Derivatives of a pulled-back band-limited function.** Let `M` be a natural number. There is
`K`, depending only on `J`, `L` and `M`, with the following property. Let `J⁻¹ ≤ |det DΦ|`, let
the derivatives of `Φ` of orders `1` to `M` be bounded by `L`, let `g` be a function of temperate
growth whose derivatives of order at most `M` are bounded by `G`, and let `f ∈ Lᵖ` have Fourier
transform vanishing outside the closed ball of radius `R > 0`. Then `∂_{m₁} ⋯ ∂_{m_M} (g Φ^* f)`
is an `Lᵖ` function of norm at most `K G (max 1 R) ^ M ‖m₁‖ ⋯ ‖m_M‖ ‖f‖_p`. -/
private theorem exists_iteratedLineDerivOp_smulLeftCLM_compCLM_eq_and_norm_le {J : ℝ} (hJ : 1 ≤ J)
    (L : ℝ) (M : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {Φ : E ≃ E} (hΦ : (Φ : E → E).HasTemperateGrowth)
      (hΨ : (Φ.symm : E → E).HasTemperateGrowth), (∀ x, J⁻¹ ≤ |(fderiv ℝ Φ x).det|) →
      (∀ n, 1 ≤ n → n ≤ M → ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ L) →
      ∀ {g : E → ℂ} {G : ℝ}, g.HasTemperateGrowth →
      (∀ n ≤ M, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ G) → ∀ {R : ℝ}, 0 < R →
      ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ → ∀ m : Fin M → E,
      ∃ w : Lp F p (volume : Measure E),
        ∂^{m} (smulLeftCLM F g (compCLM F Φ hΦ hΨ (f : 𝓢'(E, F)))) = w ∧
        ‖w‖ ≤ K * G * max 1 R ^ M * (∏ i, ‖m i‖) * ‖f‖ := by
  induction M with
  | zero =>
    refine ⟨J, zero_le_one.trans hJ, fun {p} _ {Φ} hΦ hΨ hdet _ {g G} hg hgG R _ f _ m ↦ ?_⟩
    obtain ⟨v, hv, hvn⟩ := exists_compCLM_eq_and_norm_le (F := F) hΦ hΨ hJ hdet f
    obtain ⟨w, hw, hwn⟩ := Lp.exists_smulLeftCLM_toTemperedDistribution_eq_and_norm_le hg
      (nonneg_and_norm_le_of_norm_iteratedFDeriv_le hgG).2 v
    refine ⟨w, by rw [LineDeriv.iteratedLineDerivOp_fin_zero, hv, hw], ?_⟩
    have hG := (nonneg_and_norm_le_of_norm_iteratedFDeriv_le hgG).1
    calc ‖w‖ ≤ G * (J * ‖f‖) := hwn.trans (by gcongr)
      _ = _ := by simp; ring
  | succ M ih => exact exists_iteratedLineDerivOp_smulLeftCLM_compCLM_eq_and_norm_le_succ L ih

/-- There is `K`, depending only on the bump `φ` and on `J`, such that for `J⁻¹ ≤ |det DΦ|`, a
function `g` of temperate growth bounded by `G` and `f ∈ Lᵖ`, every block `Δⱼ (g Φ^* f)` is an `Lᵖ`
function of norm at most `K G ‖f‖_p`. -/
private theorem exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le_of_norm_le
    (φ : ContDiffBump (0 : E)) {J : ℝ} (hJ : 1 ≤ J) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {Φ : E ≃ E} (hΦ : (Φ : E → E).HasTemperateGrowth)
      (hΨ : (Φ.symm : E → E).HasTemperateGrowth), (∀ x, J⁻¹ ≤ |(fderiv ℝ Φ x).det|) →
      ∀ {g : E → ℂ} {G : ℝ}, g.HasTemperateGrowth → (∀ x, ‖g x‖ ≤ G) →
      ∀ (j : ℕ) (f : Lp F p (volume : Measure E)), ∃ v : Lp F p (volume : Measure E),
        littlewoodPaleyBlock F φ j (smulLeftCLM F g (compCLM F Φ hΦ hΨ (f : 𝓢'(E, F)))) = v ∧
        ‖v‖ ≤ K * G * ‖f‖ := by
  obtain ⟨CΔ, hΔ⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  refine ⟨max CΔ 0 * J, by positivity, fun {p} _ {Φ} hΦ hΨ hdet {g G} hg hgG j f ↦ ?_⟩
  obtain ⟨u, hu, hun⟩ := exists_compCLM_eq_and_norm_le (F := F) hΦ hΨ hJ hdet f
  obtain ⟨h, hh, hhn⟩ := Lp.exists_smulLeftCLM_toTemperedDistribution_eq_and_norm_le hg hgG u
  obtain ⟨w, hw, hwn⟩ := hΔ j h
  refine ⟨w, by rw [hu, hh, hw], ?_⟩
  have hG : 0 ≤ G := (norm_nonneg _).trans (hgG 0)
  calc ‖w‖ ≤ max CΔ 0 * (G * (J * ‖f‖)) :=
        hwn.trans (mul_le_mul (le_max_left _ _) (hhn.trans (by gcongr)) (norm_nonneg _)
          (le_max_right _ _))
    _ = _ := by ring

/-- **High output frequency, low input frequency.** Let `M` be a natural number. There is `K`,
depending only on `φ`, `J`, `L` and `M`, with the following property. Let `J⁻¹ ≤ |det DΦ|` and let
the derivatives of `Φ` of orders `1` to `M` be bounded by `L`. Let `g` be a function of temperate
growth whose derivatives of order at most `M` are bounded by `G`, and let `f ∈ Lᵖ` have spectrum in
the ball of radius `2^k φ.rOut`. Then for `j > k` the block `Δⱼ (g Φ^* f)` is an `Lᵖ` function of
norm at most `K G (2^k / 2^j)^M ‖f‖_p`. -/
private theorem exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le_of_lt
    (φ : ContDiffBump (0 : E)) {J : ℝ} (hJ : 1 ≤ J) (L : ℝ) (M : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {Φ : E ≃ E} (hΦ : (Φ : E → E).HasTemperateGrowth)
      (hΨ : (Φ.symm : E → E).HasTemperateGrowth), (∀ x, J⁻¹ ≤ |(fderiv ℝ Φ x).det|) →
      (∀ n, 1 ≤ n → n ≤ M → ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ L) →
      ∀ {g : E → ℂ} {G : ℝ}, g.HasTemperateGrowth →
      (∀ n ≤ M, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ G) → ∀ {j k : ℕ}, k < j →
      ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 (2 ^ k * φ.rOut))ᶜ →
      ∃ v : Lp F p (volume : Measure E),
        littlewoodPaleyBlock F φ j (smulLeftCLM F g (compCLM F Φ hΦ hΨ (f : 𝓢'(E, F)))) = v ∧
        ‖v‖ ≤ K * G * ((2 : ℝ) ^ k / 2 ^ j) ^ M * ‖f‖ := by
  -- On the annulus carrying `Δⱼ`, the reverse Bernstein inequality bounds `Δⱼ (g Φ^* f)` by
  -- `2^{-jM}` times its derivatives of order `M`, which are `O(2^{kM})`.
  obtain ⟨C, hC, hblock⟩ := exists_norm_littlewoodPaleyBlock_succ_le_of_iteratedLineDerivOp
    (F := F) φ M
  obtain ⟨CL, hCL, hder⟩ :=
    exists_iteratedLineDerivOp_smulLeftCLM_compCLM_eq_and_norm_le (E := E) (F := F) hJ L M
  obtain ⟨K₀, -, h₀⟩ :=
    exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le_of_norm_le (F := F) φ hJ
  refine ⟨C * CL * (2 * max 1 φ.rOut) ^ M, by positivity,
    fun {p} _ {Φ} hΦ hΨ hdet hΦL {g G} hg hgG {j k} hkj f hf ↦ ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨hG, hg₀⟩ := nonneg_and_norm_le_of_norm_iteratedFDeriv_le hgG
  obtain ⟨w, hw, -⟩ := h₀ hΦ hΨ hdet hg hg₀ (j + 1) f
  refine ⟨w, hw, ?_⟩
  have hmax : max 1 (2 ^ k * φ.rOut) ≤ 2 ^ k * max 1 φ.rOut := by
    have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ one_le_two
    refine max_le ?_ ?_
    · nlinarith [le_max_left 1 φ.rOut]
    · exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
  have hR' : (0 : ℝ) < 2 ^ k * φ.rOut := by have := φ.rOut_pos; positivity
  refine (hblock j _ w hw (A := CL * G * (2 ^ k * max 1 φ.rOut) ^ M * ‖f‖)
    fun i ↦ ?_).trans_eq ?_
  · obtain ⟨y, hy, hyn⟩ := hder hΦ hΨ hdet hΦL hg hgG hR' f hf (stdOrthonormalBasis ℝ E ∘ i)
    refine ⟨y, hy, hyn.trans ?_⟩
    simp only [Function.comp_apply, OrthonormalBasis.norm_eq_one, Finset.prod_const_one, mul_one]
    gcongr
  · rw [div_pow, pow_succ, mul_pow, mul_pow, mul_pow]
    field_simp

omit [MeasurableSpace E] [BorelSpace E] in
/-- The coefficients `dₗ` of `DΦ⁻¹(Φ x) v = ∑ₗ dₗ(x) bₗ`, multiplied by a function `g` of temperate
growth, have temperate growth, and the derivatives of `dₗ g` of order at most `M` are bounded in
terms of those of `Φ`, `Φ⁻¹` and `g`. -/
private theorem hasTemperateGrowth_and_norm_iteratedFDeriv_repr_fderiv_comp_mul_le {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℝ E) {Φ : E ≃ E} (hΦ : (Φ : E → E).HasTemperateGrowth)
    (hΨ : (Φ.symm : E → E).HasTemperateGrowth) {M : ℕ} {L : ℝ}
    (hΦL : ∀ n, 1 ≤ n → n ≤ M → ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ L)
    (hΨL : ∀ n, 1 ≤ n → n ≤ M + 1 → ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ L) {g : E → ℂ} {G : ℝ}
    (hg : g.HasTemperateGrowth) (hgG : ∀ n ≤ M, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ G) (v : E)
    (l : ι) :
    ((fun x ↦ ((b.toBasis.repr (fderiv ℝ Φ.symm (Φ x) v) l : ℝ) : ℂ)) * g).HasTemperateGrowth ∧
      ∀ n ≤ M, ∀ x, ‖iteratedFDeriv ℝ n
        ((fun x ↦ ((b.toBasis.repr (fderiv ℝ Φ.symm (Φ x) v) l : ℝ) : ℂ)) * g) x‖ ≤
          2 ^ M * (M.factorial * (L * ‖v‖) * max 1 L ^ M * G) := by
  have hd : (fun x ↦ ((b.toBasis.repr (fderiv ℝ Φ.symm (Φ x) v) l : ℝ) : ℂ)).HasTemperateGrowth :=
    (hΨ.basis_repr_fderiv_apply b.toBasis v l).comp hΦ
  exact ⟨hd.mul hg, fun n hn x ↦ (hd.1.of_le (mod_cast le_top)).norm_iteratedFDeriv_mul_le_two_pow
    (hg.1.of_le (mod_cast le_top))
    (fun n hn ↦ norm_iteratedFDeriv_repr_fderiv_comp_le b hΦ.1 hΨ.1 hΦL hΨL v l n hn x)
    (fun n hn ↦ hgG n hn x) n hn⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] in
/-- The estimate of one term of the inductive step on annuli: if `‖y‖ ≤ a t Q h` and
`‖z‖ ≤ Q h`, with `1 ≤ t`, then `‖y - z‖ ≤ (a + 1) t Q h`. -/
private theorem norm_sub_le_add_one_mul {X : Type*} [SeminormedAddCommGroup X] {y z : X}
    {a t Q h : ℝ} (ht : 1 ≤ t) (hQh : 0 ≤ Q * h) (hy : ‖y‖ ≤ a * t * (Q * h))
    (hz : ‖z‖ ≤ Q * h) : ‖y - z‖ ≤ (a + 1) * t * (Q * h) :=
  (norm_sub_le _ _).trans (by nlinarith)

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
/-- The chain rule for `Φ⁻¹` and the Leibniz rule move a derivative off `T`:
`g Φ^* (∂_v T) = ∑ₗ (∂_{bₗ} (dₗ g Φ^* T) - ∂_{bₗ} (dₗ g) Φ^* T)`, where
`DΦ⁻¹(Φ x) v = ∑ₗ dₗ(x) bₗ`. -/
private theorem smulLeftCLM_compCLM_lineDerivOp {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {Φ : E ≃ E} (hΦ : (Φ : E → E).HasTemperateGrowth)
    (hΨ : (Φ.symm : E → E).HasTemperateGrowth) {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (T : 𝓢'(E, F)) (v : E) :
    smulLeftCLM F g (compCLM F Φ hΦ hΨ (∂_{v} T)) = ∑ l,
      (∂_{b l} (smulLeftCLM F
          ((fun x ↦ ((b.toBasis.repr (fderiv ℝ Φ.symm (Φ x) v) l : ℝ) : ℂ)) * g)
          (compCLM F Φ hΦ hΨ T)) -
        smulLeftCLM F (fun x ↦ fderiv ℝ
          ((fun x ↦ ((b.toBasis.repr (fderiv ℝ Φ.symm (Φ x) v) l : ℝ) : ℂ)) * g) x (b l))
          (compCLM F Φ hΦ hΨ T)) := by
  rw [compCLM_lineDerivOp b.toBasis hΦ hΨ, map_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  have hd : (fun x ↦ ((b.toBasis.repr (fderiv ℝ Φ.symm (Φ x) v) l : ℝ) : ℂ)).HasTemperateGrowth :=
    (hΨ.basis_repr_fderiv_apply b.toBasis v l).comp hΦ
  rw [smulLeftCLM_smulLeftCLM_apply hd hg, lineDerivOp_smulLeftCLM (hd.mul hg),
    OrthonormalBasis.coe_toBasis]
  abel

/-- The inductive step of
`exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le_of_annulus`. On the annulus,
`f = ∑ᵢ ∂_{bᵢ} hᵢ` with `‖hᵢ‖_p` of order `R⁻¹ ‖f‖_p`. By the chain rule
`Φ^* (∂_{bᵢ} hᵢ) = ∑ₗ dᵢₗ ∂_{bₗ} (Φ^* hᵢ)`, and
`g dᵢₗ ∂_{bₗ} Y = ∂_{bₗ} (g dᵢₗ Y) - ∂_{bₗ} (g dᵢₗ) Y`; Bernstein's inequality bounds `∂_{bₗ}` on
the spectrum of `Δⱼ` by `2^j`. So a bound of order `M` gives one of order `M + 1`. -/
private theorem exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le_of_annulus_succ
    (φ : ContDiffBump (0 : E)) {J : ℝ} (L B : ℝ) {M : ℕ}
    (ih :
      ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {Φ : E ≃ E} (hΦ : (Φ : E → E).HasTemperateGrowth)
        (hΨ : (Φ.symm : E → E).HasTemperateGrowth), (∀ x, J⁻¹ ≤ |(fderiv ℝ Φ x).det|) →
        (∀ n, 1 ≤ n → n ≤ M → ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ L) →
        (∀ n, 1 ≤ n → n ≤ M + 1 → ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ L) →
        ∀ {g : E → ℂ} {G : ℝ}, g.HasTemperateGrowth →
        (∀ n ≤ M, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ G) → ∀ (j : ℕ) {R : ℝ}, 0 < R →
        ∀ f : Lp F p (volume : Measure E),
        IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (ball 0 R ∪ (closedBall 0 (B * R))ᶜ) →
        ∃ v : Lp F p (volume : Measure E),
          littlewoodPaleyBlock F φ j (smulLeftCLM F g (compCLM F Φ hΦ hΨ (f : 𝓢'(E, F)))) = v ∧
          ‖v‖ ≤ K * G * ((2 : ℝ) ^ j / R) ^ M * ‖f‖) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {Φ : E ≃ E} (hΦ : (Φ : E → E).HasTemperateGrowth)
      (hΨ : (Φ.symm : E → E).HasTemperateGrowth), (∀ x, J⁻¹ ≤ |(fderiv ℝ Φ x).det|) →
      (∀ n, 1 ≤ n → n ≤ M + 1 → ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ L) →
      (∀ n, 1 ≤ n → n ≤ M + 1 + 1 → ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ L) →
      ∀ {g : E → ℂ} {G : ℝ}, g.HasTemperateGrowth →
      (∀ n ≤ M + 1, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ G) → ∀ (j : ℕ) {R : ℝ}, 0 < R →
      ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (ball 0 R ∪ (closedBall 0 (B * R))ᶜ) →
      ∃ v : Lp F p (volume : Measure E),
        littlewoodPaleyBlock F φ j (smulLeftCLM F g (compCLM F Φ hΦ hΨ (f : 𝓢'(E, F)))) = v ∧
        ‖v‖ ≤ K * G * ((2 : ℝ) ^ j / R) ^ (M + 1) * ‖f‖ := by
  set b := stdOrthonormalBasis ℝ E
  set d := Module.finrank ℝ E
  obtain ⟨Crep, hCrep, hrep⟩ := b.exists_eq_sum_lineDerivOp_and_norm_le (F := F) B
  obtain ⟨CB, hCB, hB⟩ :=
    exists_lineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier (E := E) (F := F)
  obtain ⟨K, hK, hKb⟩ := ih
  refine ⟨d * d * Crep * (CB * φ.rOut + 1) * K *
    (2 ^ (M + 1) * ((M + 1).factorial * max L 0 * max 1 L ^ (M + 1))), by
    have := φ.rOut_pos; positivity,
    fun {p} _ {Φ} hΦ hΨ hdet hΦL hΨL {g G} hg hgG j R hR f hf ↦ ?_⟩
  rw [max_eq_left ((norm_nonneg _).trans (hΦL 1 le_rfl (by omega) 0))]
  have hG : 0 ≤ G := (nonneg_and_norm_le_of_norm_iteratedFDeriv_le hgG).1
  obtain ⟨h, hfh, hh⟩ := hrep hR f hf
  -- The coefficients `dᵢₗ` of `DΦ⁻¹(Φ x) bᵢ = ∑ₗ dᵢₗ(x) bₗ`, and the products `g dᵢₗ`.
  set c : Fin d → Fin d → E → ℂ := fun i l ↦
    (fun x ↦ ((b.toBasis.repr (fderiv ℝ Φ.symm (Φ x) (b i)) l : ℝ) : ℂ)) * g
  have hc (i l) := hasTemperateGrowth_and_norm_iteratedFDeriv_repr_fderiv_comp_mul_le b hΦ hΨ
    hΦL hΨL hg hgG (b i) l
  simp only [b.orthonormal.1 _, mul_one] at hc
  have hΦL' : ∀ n, 1 ≤ n → n ≤ M → ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ L :=
    fun n h₁ h₂ ↦ hΦL n h₁ (by omega)
  have hΨL' : ∀ n, 1 ≤ n → n ≤ M + 1 → ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ L :=
    fun n h₁ h₂ ↦ hΨL n h₁ (by omega)
  -- `Δⱼ (g dᵢₗ Φ^* hᵢ)` is band-limited to the ball of radius `2^j φ.rOut`.
  choose y hy hyn using fun i l ↦ hKb hΦ hΨ hdet hΦL' hΨL' (hc i l).1
    (fun n hn ↦ (hc i l).2 n (by omega)) j hR (h i) (hh i).1
  have hR' : (0 : ℝ) < 2 ^ j * φ.rOut := by have := φ.rOut_pos; positivity
  choose y' hy' hy'n using fun i l ↦ hB hR' (y i l) (by
    rw [← hy i l]; exact isVanishingOn_fourier_littlewoodPaleyBlock φ j _) (b l)
  choose z hz hzn using fun i l ↦ hKb hΦ hΨ hdet hΦL' hΨL' ((hc i l).1.fderiv_apply (b l))
    ((hc i l).1.1.norm_iteratedFDeriv_fderiv_apply_le_of_forall_le (by
      rw [minSmoothness_of_isRCLikeNormedField]; exact_mod_cast le_top) (hc i l).2 (b l))
    j hR (h i) (hh i).1
  refine ⟨∑ i, ∑ l, (y' i l - z i l), ?_, ?_⟩
  · rw [hfh, map_sum, map_sum, map_sum]
    simp_rw [smulLeftCLM_compCLM_lineDerivOp b hΦ hΨ hg, map_sum, map_sub,
      littlewoodPaleyBlock_lineDerivOp, hy, hy', hz, Lp.toTemperedDistribution_sum,
      Lp.toTemperedDistribution_sub]
  · -- Each term is at most `(CB φ.rOut + 1) 2^j Q ‖hᵢ‖`, and `‖hᵢ‖ ≤ Crep R⁻¹ ‖f‖`.
    set Q := K * (2 ^ (M + 1) * ((M + 1).factorial * L * max 1 L ^ (M + 1) * G)) *
      ((2 : ℝ) ^ j / R) ^ M
    have hQ : 0 ≤ Q := by
      have := (norm_nonneg _).trans (hΦL 1 le_rfl (by omega) 0); positivity
    have hterm (i l) : ‖y' i l - z i l‖ ≤ (CB * φ.rOut + 1) * 2 ^ j * (Q * (Crep / R * ‖f‖)) := by
      have hy'i := hy'n i l
      rw [b.orthonormal.1 l, mul_one] at hy'i
      have hzi : ‖z i l‖ ≤ Q * ‖h i‖ := by simpa [b.orthonormal.1 l] using hzn i l
      refine (norm_sub_le_add_one_mul (a := CB * φ.rOut) (t := 2 ^ j) (Q := Q) (h := ‖h i‖)
        (one_le_pow₀ one_le_two) (by positivity) (hy'i.trans ?_) hzi).trans ?_
      · rw [show CB * φ.rOut * 2 ^ j * (Q * ‖h i‖) = CB * (2 ^ j * φ.rOut) * (Q * ‖h i‖) by
          ring]
        have := φ.rOut_pos
        gcongr
        exact hyn i l
      · have := φ.rOut_pos
        gcongr
        exact (hh i).2
    calc ‖∑ i, ∑ l, (y' i l - z i l)‖ ≤ ∑ i, ∑ l, ‖y' i l - z i l‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ norm_sum_le _ _)
      _ ≤ ∑ _i : Fin d, ∑ _l : Fin d, (CB * φ.rOut + 1) * 2 ^ j * (Q * (Crep / R * ‖f‖)) :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun l _ ↦ hterm i l
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Q]
        rw [pow_succ ((2 : ℝ) ^ j / R)]
        field_simp

/-- **Low output frequency, high input frequency.** Let `B` be a real number and `M` a natural
number. There is `K`, depending only on `φ`, `J`, `L`, `B` and `M`, with the following property.
Let `J⁻¹ ≤ |det DΦ|`, let the derivatives of `Φ` of orders `1` to `M` and those of `Φ⁻¹` of orders
`1` to `M + 1` be bounded by `L`. Let `g` be a function of temperate growth whose derivatives of
order at most `M` are bounded by `G`, and let `f ∈ Lᵖ` have spectrum in the annulus
`R ≤ ‖ξ‖ ≤ B R`. Then every block `Δⱼ (g Φ^* f)` is an `Lᵖ` function of norm at most
`K G (2^j / R)^M ‖f‖_p`. -/
private theorem exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le_of_annulus
    (φ : ContDiffBump (0 : E)) {J : ℝ} (hJ : 1 ≤ J) (L B : ℝ) (M : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {Φ : E ≃ E} (hΦ : (Φ : E → E).HasTemperateGrowth)
      (hΨ : (Φ.symm : E → E).HasTemperateGrowth), (∀ x, J⁻¹ ≤ |(fderiv ℝ Φ x).det|) →
      (∀ n, 1 ≤ n → n ≤ M → ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ L) →
      (∀ n, 1 ≤ n → n ≤ M + 1 → ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ L) →
      ∀ {g : E → ℂ} {G : ℝ}, g.HasTemperateGrowth →
      (∀ n ≤ M, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ G) → ∀ (j : ℕ) {R : ℝ}, 0 < R →
      ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (ball 0 R ∪ (closedBall 0 (B * R))ᶜ) →
      ∃ v : Lp F p (volume : Measure E),
        littlewoodPaleyBlock F φ j (smulLeftCLM F g (compCLM F Φ hΦ hΨ (f : 𝓢'(E, F)))) = v ∧
        ‖v‖ ≤ K * G * ((2 : ℝ) ^ j / R) ^ M * ‖f‖ := by
  -- Induction on `M`: each step gains `2^j / R`.
  obtain ⟨K₀, hK₀, h₀⟩ :=
    exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le_of_norm_le (F := F) φ hJ
  induction M with
  | zero =>
    refine ⟨K₀, hK₀, fun {p} _ {Φ} hΦ hΨ hdet _ _ {g G} hg hgG j R _ f _ ↦ ?_⟩
    obtain ⟨w, hw, hwn⟩ := h₀ hΦ hΨ hdet hg (nonneg_and_norm_le_of_norm_iteratedFDeriv_le hgG).2 j f
    exact ⟨w, hw, by simpa using hwn⟩
  | succ M ih =>
    exact exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le_of_annulus_succ φ L B ih

/-- **Off-diagonal decay of a multiplied pullback between Littlewood–Paley blocks.** Let `M` be a
natural number. There is `K`, depending only on `φ`, `L` and `M`, with the following property. Let
`Φ` be a bijection such that `Φ` and `Φ⁻¹` have temperate growth, the derivatives of `Φ` of orders
`1` to `M` and those of `Φ⁻¹` of orders `1` to `M + 1` being bounded by `L`, and let `g` be a
function of temperate growth whose derivatives of order at most `M` are bounded by `G`. Let
`1 ≤ p ≤ ∞`, and let the block `Δₖ u` of a tempered distribution be an `Lᵖ` function `f`. Then for
every `j` the block `Δⱼ (g Φ^* f)` is an `Lᵖ` function of norm at most
`K G 2^{-M |j - k|} ‖f‖_p`. For `g = 1` this is the block estimate for the pullback
(`TauCeti.exists_littlewoodPaleyBlock_compCLM_eq_and_norm_le`), and for `Φ = id` the one for
multiplication (`TauCeti.exists_littlewoodPaleyBlock_smulLeftCLM_eq_and_norm_le`). -/
theorem exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le (φ : ContDiffBump (0 : E))
    (L : ℝ) (M : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {Φ : E ≃ E} (hΦ : (Φ : E → E).HasTemperateGrowth)
      (hΨ : (Φ.symm : E → E).HasTemperateGrowth),
      (∀ n, 1 ≤ n → n ≤ M → ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ L) →
      (∀ n, 1 ≤ n → n ≤ M + 1 → ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ L) →
      ∀ {g : E → ℂ} {G : ℝ}, g.HasTemperateGrowth →
      (∀ n ≤ M, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ G) →
      ∀ (j k : ℕ) (u : 𝓢'(E, F)) (f : Lp F p (volume : Measure E)),
      littlewoodPaleyBlock F φ k u = f → ∃ v : Lp F p (volume : Measure E),
        littlewoodPaleyBlock F φ j (smulLeftCLM F g (compCLM F Φ hΦ hΨ (f : 𝓢'(E, F)))) = v ∧
        ‖v‖ ≤ K * G * (2 : ℝ) ^ (-(M * |(j : ℝ) - k|)) * ‖f‖ := by
  set J := max 1 L ^ Module.finrank ℝ E
  have hJ : 1 ≤ J := one_le_pow₀ (le_max_left 1 L)
  obtain ⟨K₁, hK₁, h₁⟩ :=
    exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le_of_lt (F := F) φ hJ L M
  obtain ⟨K₂, hK₂, h₂⟩ := exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le_of_annulus
    (F := F) φ hJ L (2 * φ.rOut / φ.rIn) M
  obtain ⟨K₀, hK₀, h₀⟩ :=
    exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le_of_norm_le (F := F) φ hJ
  have hrIn := φ.rIn_pos
  refine ⟨K₁ + K₂ * (2 / φ.rIn) ^ M + K₀, by positivity,
    fun {p} _ {Φ} hΦ hΨ hΦL hΨL {g G} hg hgG j k u f hf ↦ ?_⟩
  -- The Jacobian is bounded below in terms of `DΦ⁻¹`.
  have hdet : ∀ x, J⁻¹ ≤ |(fderiv ℝ Φ x).det| :=
    Φ.inv_max_one_pow_le_abs_det_fderiv (hΦ.1.differentiable (by simp))
      (hΨ.1.differentiable (by simp)) fun y ↦ by simpa using hΨL 1 le_rfl (by omega) y
  obtain ⟨hG, hg₀⟩ := nonneg_and_norm_le_of_norm_iteratedFDeriv_le hgG
  obtain ⟨v, hv, hvn⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le_of_ball_of_annulus φ
    (fun T ↦ smulLeftCLM F g (compCLM F Φ hΦ hΨ T)) (mul_nonneg hK₀ hG) (mul_nonneg hK₁ hG)
    (mul_nonneg hK₂ hG) (fun j f ↦ h₀ hΦ hΨ hdet hg hg₀ j f)
    (fun hkj f hf ↦ h₁ hΦ hΨ hdet hΦL hg hgG hkj f hf)
    (fun j _ hR f hf ↦ h₂ hΦ hΨ hdet hΦL hΨL hg hgG j hR f hf) j k u f hf
  exact ⟨v, hv, hvn.trans_eq (by ring)⟩

/-- **Off-diagonal decay of a pullback between Littlewood–Paley blocks.** Let `M` be a natural
number. There is `K`, depending only on `φ`, `L` and `M`, with the following property. Let `Φ` be
a bijection such that `Φ` and `Φ⁻¹` have temperate growth, the derivatives of `Φ` of orders `1` to
`M` and those of `Φ⁻¹` of orders `1` to `M + 1` being bounded by `L`. Let `1 ≤ p ≤ ∞`, and let the
block `Δₖ u` of a tempered distribution be an `Lᵖ` function `f`. Then for every `j` the block
`Δⱼ (Φ^* f)` is an `Lᵖ` function of norm at most `K 2^{-M |j - k|} ‖f‖_p`. -/
theorem exists_littlewoodPaleyBlock_compCLM_eq_and_norm_le (φ : ContDiffBump (0 : E)) (L : ℝ)
    (M : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {Φ : E ≃ E} (hΦ : (Φ : E → E).HasTemperateGrowth)
      (hΨ : (Φ.symm : E → E).HasTemperateGrowth),
      (∀ n, 1 ≤ n → n ≤ M → ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ L) →
      (∀ n, 1 ≤ n → n ≤ M + 1 → ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ L) →
      ∀ (j k : ℕ) (u : 𝓢'(E, F)) (f : Lp F p (volume : Measure E)),
      littlewoodPaleyBlock F φ k u = f → ∃ v : Lp F p (volume : Measure E),
        littlewoodPaleyBlock F φ j (compCLM F Φ hΦ hΨ (f : 𝓢'(E, F))) = v ∧
        ‖v‖ ≤ K * (2 : ℝ) ^ (-(M * |(j : ℝ) - k|)) * ‖f‖ := by
  -- Multiplication by the constant `1` is the identity.
  obtain ⟨K, hK, h⟩ := exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le (F := F) φ L M
  refine ⟨K, hK, fun {p} _ {Φ} hΦ hΨ hΦL hΨL j k u f hf ↦ ?_⟩
  simpa only [smulLeftCLM_const, one_smul, mul_one] using h hΦ hΨ hΦL hΨL (.const 1)
    (fun n _ x ↦ (norm_iteratedFDeriv_const_le n (1 : ℂ) x).trans_eq norm_one) j k u f hf

/-! ### Pullback on Besov spaces -/

/-- **Pullback by a diffeomorphism is bounded on Besov spaces.** Let `N` be a natural number with
`|s| < N`. There is `C`, depending only on `φ`, `s`, `N` and `L`, with the following property.
Let `Φ` be a bijection such that `Φ` and `Φ⁻¹` have temperate growth, the derivatives of `Φ` of
orders `1` to `N` and those of `Φ⁻¹` of orders `1` to `N + 1` being bounded by `L`. Then for all
`1 ≤ p, q ≤ ∞` and every `u ∈ B^s_{p,q}`, the pullback `Φ^* u` lies in `B^s_{p,q}` and
`‖Φ^* u‖ ≤ C ‖u‖`. -/
theorem BesovSpace.exists_toDistr_eq_compCLM_and_norm_le (φ : ContDiffBump (0 : E)) {s : ℝ}
    {N : ℕ} (hN : |s| < N) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Φ : E ≃ E} (hΦ : (Φ : E → E).HasTemperateGrowth)
      (hΨ : (Φ.symm : E → E).HasTemperateGrowth),
      (∀ n, 1 ≤ n → n ≤ N → ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ L) →
      (∀ n, 1 ≤ n → n ≤ N + 1 → ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ L) →
      ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (u : BesovSpace F φ s p q),
      ∃ v : BesovSpace F φ s p q, v.toDistr = compCLM F Φ hΦ hΨ u.toDistr ∧ ‖v‖ ≤ C * ‖u‖ := by
  -- `Φ^*` is almost diagonal: its interaction between the blocks `j` and `k` decays like
  -- `2^{-N |j - k|}`.
  obtain ⟨K, hK, hblock⟩ := exists_littlewoodPaleyBlock_compCLM_eq_and_norm_le (F := F) φ L N
  refine ⟨K * ∑' d : ℤ, ((2 : ℝ) ^ (|s| - N)) ^ d.natAbs, by positivity,
    fun {Φ} hΦ hΨ hΦL hΨL {p q} _ _ u ↦ ?_⟩
  exact exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_le (compCLM F Φ hΦ hΨ) hN hK u
    fun j k ↦ hblock hΦ hΨ hΦL hΨL j k u.toDistr (u.block k) (u.coe_block k).symm

/-- The pullback `Φ^*` is bounded on `B^s_{p,q}` under the derivative bounds of
`TemperedDistribution.MemBesov.compCLM`. -/
private theorem BesovSpace.exists_toDistr_eq_compCLM_and_norm_le_of_forall_exists
    {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {Φ : E ≃ E}
    (hΦ : (Φ : E → E).HasTemperateGrowth) (hΨ : (Φ.symm : E → E).HasTemperateGrowth)
    (hΦb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C)
    (hΨb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C) :
    ∃ C : ℝ, ∀ u : BesovSpace F φ s p q, ∃ v : BesovSpace F φ s p q,
      v.toDistr = compCLM F Φ hΦ hΨ u.toDistr ∧ ‖v‖ ≤ C * ‖u‖ := by
  obtain ⟨L₁, hL₁⟩ := exists_forall_norm_iteratedFDeriv_le_of_forall_one_le hΦb
  obtain ⟨L₂, hL₂⟩ := exists_forall_norm_iteratedFDeriv_le_of_forall_one_le hΨb
  obtain ⟨C, -, hC⟩ := exists_toDistr_eq_compCLM_and_norm_le (F := F) φ
    (N := ⌊|s|⌋₊ + 1) (by push_cast; exact Nat.lt_floor_add_one _) (max L₁ L₂)
  exact ⟨C, fun u ↦ hC hΦ hΨ (fun n h₁ h₂ x ↦ (hL₁ n h₁ h₂ x).trans (le_max_left _ _))
    (fun n h₁ h₂ x ↦ (hL₂ n h₁ h₂ x).trans (le_max_right _ _)) u⟩

end TauCeti

namespace TemperedDistribution

open TauCeti

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **Pullback of Besov distributions.** If `u ∈ B^s_{p,q}` and `Φ` is a bijection such that `Φ` and
`Φ⁻¹` have temperate growth, with bounded derivatives of `Φ` of orders `1` to `⌊|s|⌋₊ + 1` and of
`Φ⁻¹` of orders `1` to `⌊|s|⌋₊ + 2`, then `Φ^* u ∈ B^s_{p,q}`. -/
theorem MemBesov.compCLM {u : 𝓢'(E, F)} (hu : u.MemBesov φ s p q) {Φ : E ≃ E}
    (hΦ : (Φ : E → E).HasTemperateGrowth) (hΨ : (Φ.symm : E → E).HasTemperateGrowth)
    (hΦb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C)
    (hΨb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C) :
    (compCLM F Φ hΦ hΨ u).MemBesov φ s p q := by
  obtain ⟨C, hC⟩ := BesovSpace.exists_toDistr_eq_compCLM_and_norm_le_of_forall_exists (F := F)
    (φ := φ) (p := p) (q := q) hΦ hΨ hΦb hΨb
  obtain ⟨v, hv, -⟩ := hC hu.toBesovSpace
  rw [← hu.toDistr_toBesovSpace, ← hv]
  exact v.memBesov_toDistr

/-- **Pullback invariance of `MemBesov`.** If `Φ` and `Φ⁻¹` have temperate growth and bounded
derivatives of orders `1` to `⌊|s|⌋₊ + 2`, a tempered distribution `u` lies in `B^s_{p,q}` if and
only if its pullback `Φ^* u` does. -/
theorem memBesov_compCLM_iff {u : 𝓢'(E, F)} {Φ : E ≃ E}
    (hΦ : (Φ : E → E).HasTemperateGrowth) (hΨ : (Φ.symm : E → E).HasTemperateGrowth)
    (hΦb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C)
    (hΨb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C) :
    (compCLM F Φ hΦ hΨ u).MemBesov φ s p q ↔ u.MemBesov φ s p q := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.compCLM hΦ hΨ (fun n h₁ h₂ ↦ hΦb n h₁ (by omega)) hΨb⟩
  simpa only [compCLM_symm_compCLM hΦ hΨ hΦ] using
    h.compCLM hΨ hΦ (fun n h₁ h₂ ↦ hΨb n h₁ (by omega)) hΦb

end TemperedDistribution

namespace TauCeti.BesovSpace

open TemperedDistribution

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The pullback `Φ^*` on `B^s_{p,q}` is bounded, for derivative bounds as in
`TemperedDistribution.MemBesov.compCLM`. -/
private theorem exists_norm_compCLM_toBesovSpace_le {Φ : E ≃ E}
    (hΦ : (Φ : E → E).HasTemperateGrowth) (hΨ : (Φ.symm : E → E).HasTemperateGrowth)
    (hΦb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C)
    (hΨb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C) :
    ∃ C, ∀ u : BesovSpace F φ s p q,
      ‖(u.memBesov_toDistr.compCLM hΦ hΨ hΦb hΨb).toBesovSpace‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC⟩ := exists_toDistr_eq_compCLM_and_norm_le_of_forall_exists (F := F) (φ := φ)
    (p := p) (q := q) hΦ hΨ hΦb hΨb
  refine ⟨C, fun u ↦ ?_⟩
  obtain ⟨v, hv, hvn⟩ := hC u
  have : (u.memBesov_toDistr.compCLM hΦ hΨ hΦb hΨb).toBesovSpace = v := ext (by simp [hv])
  rwa [this]

variable (F φ s p q) in
/-- **Pullback by a diffeomorphism with bounded derivatives**, as an isomorphism of `B^s_{p,q}`.
Here `Φ` is a bijection such that `Φ` and `Φ⁻¹` have temperate growth and bounded derivatives of
orders `1` to `⌊|s|⌋₊ + 2`. The inverse is the pullback along `Φ⁻¹`
(`TauCeti.BesovSpace.compCLE_symm`), and the operator norm is bounded in terms of `φ`, `s` and the
bounds for these derivatives only (`TauCeti.BesovSpace.exists_norm_compCLE_le`). -/
def compCLE (Φ : E ≃ E) (hΦ : (Φ : E → E).HasTemperateGrowth)
    (hΨ : (Φ.symm : E → E).HasTemperateGrowth)
    (hΦb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C)
    (hΨb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C) :
    BesovSpace F φ s p q ≃L[ℂ] BesovSpace F φ s p q :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    { toFun u := (u.memBesov_toDistr.compCLM hΦ hΨ (fun n h₁ h₂ ↦ hΦb n h₁ (by omega))
        hΨb).toBesovSpace
      invFun v := (v.memBesov_toDistr.compCLM (Φ := Φ.symm) hΨ hΦ
        (fun n h₁ h₂ ↦ hΨb n h₁ (by omega)) hΦb).toBesovSpace
      map_add' _ _ := ext (by simp)
      map_smul' _ _ := ext (by simp)
      left_inv u := ext (by simp)
      right_inv v := ext (by simp) }
    _ _ (exists_norm_compCLM_toBesovSpace_le (F := F) (φ := φ) (p := p) (q := q) hΦ hΨ
      (fun n h₁ h₂ ↦ hΦb n h₁ (by omega)) hΨb).choose_spec
    (exists_norm_compCLM_toBesovSpace_le (F := F) (φ := φ) (p := p) (q := q) (Φ := Φ.symm) hΨ hΦ
      (fun n h₁ h₂ ↦ hΨb n h₁ (by omega)) hΦb).choose_spec

variable {Φ : E ≃ E} {hΦ : (Φ : E → E).HasTemperateGrowth}
  {hΨ : (Φ.symm : E → E).HasTemperateGrowth}
  {hΦb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C}
  {hΨb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C}

@[simp]
theorem toDistr_compCLE (u : BesovSpace F φ s p q) :
    (compCLE F φ s p q Φ hΦ hΨ hΦb hΨb u).toDistr =
      TemperedDistribution.compCLM F Φ hΦ hΨ u.toDistr := by
  simp [compCLE, LinearEquiv.toContinuousLinearEquivOfBounds,
    MemBesov.toDistr_toBesovSpace]

/-- The inverse of the pullback along `Φ` is the pullback along `Φ⁻¹`. -/
@[simp]
theorem compCLE_symm :
    (compCLE F φ s p q Φ hΦ hΨ hΦb hΨb).symm = compCLE F φ s p q Φ.symm hΨ hΦ hΨb hΦb := by
  refine ContinuousLinearEquiv.ext (funext fun u ↦ ?_)
  rw [ContinuousLinearEquiv.symm_apply_eq]
  exact ext (by simp)

/-- **The norm of the pullback on Besov spaces.** There is `C`, depending only on `φ`, `s` and `L`,
with the following property. If the derivatives of `Φ` and of `Φ⁻¹` of orders `1` to `⌊|s|⌋₊ + 2`
are bounded by `L`, then the pullback along `Φ` has operator norm at most `C` on `B^s_{p,q}` for
all `1 ≤ p, q ≤ ∞`. -/
theorem exists_norm_compCLE_le (φ : ContDiffBump (0 : E)) (s L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {Φ : E ≃ E}
      (hΦ : (Φ : E → E).HasTemperateGrowth) (hΨ : (Φ.symm : E → E).HasTemperateGrowth)
      (hΦb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C)
      (hΨb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C),
      (∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ L) →
      (∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ L) →
      ‖(compCLE F φ s p q Φ hΦ hΨ hΦb hΨb : BesovSpace F φ s p q →L[ℂ] BesovSpace F φ s p q)‖ ≤
        C := by
  obtain ⟨C, hC, hpull⟩ := exists_toDistr_eq_compCLM_and_norm_le (F := F) φ
    (N := ⌊|s|⌋₊ + 1) (by push_cast; exact Nat.lt_floor_add_one _) L
  refine ⟨C, hC, fun {p q} _ _ Φ hΦ hΨ hΦb hΨb hΦL hΨL ↦
    ContinuousLinearMap.opNorm_le_bound _ hC fun u ↦ ?_⟩
  obtain ⟨v, hv, hvn⟩ := hpull hΦ hΨ (fun n h₁ h₂ ↦ hΦL n h₁ (by omega)) hΨL (p := p) (q := q) u
  have : compCLE F φ s p q Φ hΦ hΨ hΦb hΨb u = v := ext (by simp [hv])
  simpa [this] using hvn

@[simp]
theorem compCLE_refl (h₁ : (Equiv.refl E : E → E).HasTemperateGrowth)
    (h₂ : ((Equiv.refl E).symm : E → E).HasTemperateGrowth)
    (hb₁ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (Equiv.refl E) x‖ ≤ C)
    (hb₂ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 →
      ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (Equiv.refl E).symm x‖ ≤ C) :
    compCLE F φ s p q (Equiv.refl E) h₁ h₂ hb₁ hb₂ = ContinuousLinearEquiv.refl ℂ _ := by
  ext u : 3
  simp [TemperedDistribution.compCLM_refl]

/-- **Contravariant functoriality of the pullback on Besov spaces**: `(Φ₂ ∘ Φ₁)^* = Φ₁^* ∘ Φ₂^*`. -/
theorem compCLE_trans {Φ₁ Φ₂ : E ≃ E}
    (hΦ₁ : (Φ₁ : E → E).HasTemperateGrowth) (hΨ₁ : (Φ₁.symm : E → E).HasTemperateGrowth)
    (hΦ₁b : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ₁ x‖ ≤ C)
    (hΨ₁b : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ₁.symm x‖ ≤ C)
    (hΦ₂ : (Φ₂ : E → E).HasTemperateGrowth) (hΨ₂ : (Φ₂.symm : E → E).HasTemperateGrowth)
    (hΦ₂b : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ₂ x‖ ≤ C)
    (hΨ₂b : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ₂.symm x‖ ≤ C)
    (h₁ : (Φ₁.trans Φ₂ : E → E).HasTemperateGrowth)
    (h₂ : ((Φ₁.trans Φ₂).symm : E → E).HasTemperateGrowth)
    (hb₁ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (Φ₁.trans Φ₂) x‖ ≤ C)
    (hb₂ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 →
      ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (Φ₁.trans Φ₂).symm x‖ ≤ C) :
    compCLE F φ s p q (Φ₁.trans Φ₂) h₁ h₂ hb₁ hb₂ =
      (compCLE F φ s p q Φ₂ hΦ₂ hΨ₂ hΦ₂b hΨ₂b).trans (compCLE F φ s p q Φ₁ hΦ₁ hΨ₁ hΦ₁b hΨ₁b) := by
  ext u : 3
  simp [TemperedDistribution.compCLM_trans hΦ₁ hΨ₁ hΦ₂ hΨ₂ h₁ h₂]

/-! ### Pullback by a diffeomorphism as a bounded operator -/

variable (F φ s p q) in
/-- **Pullback by a diffeomorphism with bounded derivatives**, as a bounded operator on
`B^s_{p,q}`, under the derivative bounds of `TemperedDistribution.MemBesov.compCLM`: those of `Φ`
of orders `1` to `⌊|s|⌋₊ + 1` and those of `Φ⁻¹` of orders `1` to `⌊|s|⌋₊ + 2`. Its norm is
bounded uniformly in `p` and `q` (`TauCeti.BesovSpace.exists_norm_compCLM_le`). When `Φ` also has
bounded derivatives of order `⌊|s|⌋₊ + 2`, it is the isomorphism `TauCeti.BesovSpace.compCLE`
(`TauCeti.BesovSpace.compCLE_apply`). -/
def compCLM (Φ : E ≃ E) (hΦ : (Φ : E → E).HasTemperateGrowth)
    (hΨ : (Φ.symm : E → E).HasTemperateGrowth)
    (hΦb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C)
    (hΨb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C) :
    BesovSpace F φ s p q →L[ℂ] BesovSpace F φ s p q :=
  LinearMap.mkContinuousOfExistsBound
    { toFun u := (u.memBesov_toDistr.compCLM hΦ hΨ hΦb hΨb).toBesovSpace
      map_add' _ _ := ext (by simp)
      map_smul' _ _ := ext (by simp) }
    (exists_norm_compCLM_toBesovSpace_le hΦ hΨ hΦb hΨb)

section CompCLM

variable {Φ : E ≃ E} {hΦ : (Φ : E → E).HasTemperateGrowth}
  {hΨ : (Φ.symm : E → E).HasTemperateGrowth}
  {hΦb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C}
  {hΨb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C}

@[simp]
theorem toDistr_compCLM (u : BesovSpace F φ s p q) :
    (compCLM F φ s p q Φ hΦ hΨ hΦb hΨb u).toDistr =
      TemperedDistribution.compCLM F Φ hΦ hΨ u.toDistr := by
  simp [compCLM]

/-- The isomorphism `TauCeti.BesovSpace.compCLE` acts as the operator
`TauCeti.BesovSpace.compCLM`. -/
theorem compCLE_apply
    (hΦb' : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C)
    (u : BesovSpace F φ s p q) :
    compCLE F φ s p q Φ hΦ hΨ hΦb' hΨb u = compCLM F φ s p q Φ hΦ hΨ hΦb hΨb u :=
  ext (by simp)

/-- Pulling back along `Φ` and then along `Φ⁻¹` gives back the Besov element. -/
@[simp]
theorem compCLM_symm_compCLM
    (hΦ' : (Φ.symm.symm : E → E).HasTemperateGrowth)
    (hΨb' : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C)
    (hΦb' : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm.symm x‖ ≤ C)
    (u : BesovSpace F φ s p q) :
    compCLM F φ s p q Φ.symm hΨ hΦ' hΨb' hΦb' (compCLM F φ s p q Φ hΦ hΨ hΦb hΨb u) = u :=
  ext (by simp)

/-- Pulling back along `Φ⁻¹` and then along `Φ` gives back the Besov element. -/
@[simp]
theorem compCLM_compCLM_symm
    (hΦ' : (Φ.symm.symm : E → E).HasTemperateGrowth)
    (hΨb' : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C)
    (hΦb' : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm.symm x‖ ≤ C)
    (u : BesovSpace F φ s p q) :
    compCLM F φ s p q Φ hΦ hΨ hΦb hΨb (compCLM F φ s p q Φ.symm hΨ hΦ' hΨb' hΦb' u) = u :=
  ext (by simp)

end CompCLM

/-- **The norm of the pullback on Besov spaces.** Let `N` be a natural number with `|s| < N`.
There is `C`, depending only on `φ`, `s`, `N` and `L`, with the following property. If the
derivatives of `Φ` of orders `1` to `N` and those of `Φ⁻¹` of orders `1` to `N + 1` are bounded by
`L`, then `TauCeti.BesovSpace.compCLM` has operator norm at most `C` on `B^s_{p,q}` for all
`1 ≤ p, q ≤ ∞`. -/
theorem exists_norm_compCLM_le (φ : ContDiffBump (0 : E)) {N : ℕ} (hN : |s| < N) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {Φ : E ≃ E}
      (hΦ : (Φ : E → E).HasTemperateGrowth) (hΨ : (Φ.symm : E → E).HasTemperateGrowth)
      (hΦb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C)
      (hΨb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C),
      (∀ n, 1 ≤ n → n ≤ N → ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ L) →
      (∀ n, 1 ≤ n → n ≤ N + 1 → ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ L) →
      ‖compCLM F φ s p q Φ hΦ hΨ hΦb hΨb‖ ≤ C := by
  obtain ⟨C, hC, hpull⟩ := exists_toDistr_eq_compCLM_and_norm_le (F := F) φ hN L
  refine ⟨C, hC, fun {p q} _ _ Φ hΦ hΨ hΦb hΨb hΦL hΨL ↦
    ContinuousLinearMap.opNorm_le_bound _ hC fun u ↦ ?_⟩
  obtain ⟨v, hv, hvn⟩ := hpull hΦ hΨ hΦL hΨL (p := p) (q := q) u
  have : compCLM F φ s p q Φ hΦ hΨ hΦb hΨb u = v := ext (by simp [hv])
  rwa [this]

/-- Pullback along the identity is the identity of `B^s_{p,q}`. -/
@[simp]
theorem compCLM_refl (h₁ : (Equiv.refl E : E → E).HasTemperateGrowth)
    (h₂ : ((Equiv.refl E).symm : E → E).HasTemperateGrowth)
    (hb₁ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (Equiv.refl E) x‖ ≤ C)
    (hb₂ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 →
      ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (Equiv.refl E).symm x‖ ≤ C) :
    compCLM F φ s p q (Equiv.refl E) h₁ h₂ hb₁ hb₂ = ContinuousLinearMap.id ℂ _ := by
  ext u : 2
  simp [TemperedDistribution.compCLM_refl]

/-- **Contravariant functoriality of the pullback on Besov spaces**: `(Φ₂ ∘ Φ₁)^* = Φ₁^* ∘ Φ₂^*`. -/
theorem compCLM_trans {Φ₁ Φ₂ : E ≃ E}
    (hΦ₁ : (Φ₁ : E → E).HasTemperateGrowth) (hΨ₁ : (Φ₁.symm : E → E).HasTemperateGrowth)
    (hΦ₁b : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ₁ x‖ ≤ C)
    (hΨ₁b : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ₁.symm x‖ ≤ C)
    (hΦ₂ : (Φ₂ : E → E).HasTemperateGrowth) (hΨ₂ : (Φ₂.symm : E → E).HasTemperateGrowth)
    (hΦ₂b : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ₂ x‖ ≤ C)
    (hΨ₂b : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ₂.symm x‖ ≤ C)
    (h₁ : (Φ₁.trans Φ₂ : E → E).HasTemperateGrowth)
    (h₂ : ((Φ₁.trans Φ₂).symm : E → E).HasTemperateGrowth)
    (hb₁ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (Φ₁.trans Φ₂) x‖ ≤ C)
    (hb₂ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 →
      ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (Φ₁.trans Φ₂).symm x‖ ≤ C) :
    compCLM F φ s p q (Φ₁.trans Φ₂) h₁ h₂ hb₁ hb₂ =
      compCLM F φ s p q Φ₁ hΦ₁ hΨ₁ hΦ₁b hΨ₁b ∘L compCLM F φ s p q Φ₂ hΦ₂ hΨ₂ hΦ₂b hΨ₂b := by
  ext u : 2
  simp [TemperedDistribution.compCLM_trans hΦ₁ hΨ₁ hΦ₂ hΨ₂ h₁ h₂]

/-! ### Smooth diffeomorphisms with bounded derivatives of every positive order -/

variable (F φ s p q) in
/-- **Pullback by a smooth diffeomorphism with bounded derivatives**, as an isomorphism of
`B^s_{p,q}`. Here `Φ` and `Φ⁻¹` are smooth with bounded derivatives of every positive order, so
they have temperate growth (`Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_of_pos`). This
is `TauCeti.BesovSpace.compCLE` with these hypotheses. -/
def compCLEOfContDiff (Φ : E ≃ E) (hΦ : ContDiff ℝ ∞ Φ) (hΨ : ContDiff ℝ ∞ Φ.symm)
    (hΦb : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C)
    (hΨb : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C) :
    BesovSpace F φ s p q ≃L[ℂ] BesovSpace F φ s p q :=
  compCLE F φ s p q Φ (.of_norm_iteratedFDeriv_le_of_pos hΦ hΦb)
    (.of_norm_iteratedFDeriv_le_of_pos hΨ hΨb) (fun n h₁ _ ↦ hΦb n h₁) (fun n h₁ _ ↦ hΨb n h₁)

@[simp]
theorem toDistr_compCLEOfContDiff {Φ : E ≃ E} (hΦ : ContDiff ℝ ∞ Φ) (hΨ : ContDiff ℝ ∞ Φ.symm)
    (hΦb : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C)
    (hΨb : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C)
    (u : BesovSpace F φ s p q) :
    (compCLEOfContDiff F φ s p q Φ hΦ hΨ hΦb hΨb u).toDistr =
      TemperedDistribution.compCLM F Φ (.of_norm_iteratedFDeriv_le_of_pos hΦ hΦb)
        (.of_norm_iteratedFDeriv_le_of_pos hΨ hΨb) u.toDistr := by
  simp [compCLEOfContDiff]

/-- The inverse of the pullback along `Φ` is the pullback along `Φ⁻¹`. -/
@[simp]
theorem compCLEOfContDiff_symm {Φ : E ≃ E} (hΦ : ContDiff ℝ ∞ Φ) (hΨ : ContDiff ℝ ∞ Φ.symm)
    (hΦb : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C)
    (hΨb : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C) :
    (compCLEOfContDiff F φ s p q Φ hΦ hΨ hΦb hΨb).symm =
      compCLEOfContDiff F φ s p q Φ.symm hΨ hΦ hΨb hΦb :=
  compCLE_symm

@[simp]
theorem compCLEOfContDiff_refl (h₁ : ContDiff ℝ ∞ (Equiv.refl E))
    (h₂ : ContDiff ℝ ∞ (Equiv.refl E).symm)
    (hb₁ : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (Equiv.refl E) x‖ ≤ C)
    (hb₂ : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (Equiv.refl E).symm x‖ ≤ C) :
    compCLEOfContDiff F φ s p q (Equiv.refl E) h₁ h₂ hb₁ hb₂ = ContinuousLinearEquiv.refl ℂ _ :=
  compCLE_refl _ _ _ _

/-- **Contravariant functoriality of the pullback on Besov spaces**: `(Φ₂ ∘ Φ₁)^* = Φ₁^* ∘ Φ₂^*`. -/
theorem compCLEOfContDiff_trans {Φ₁ Φ₂ : E ≃ E}
    (hΦ₁ : ContDiff ℝ ∞ Φ₁) (hΨ₁ : ContDiff ℝ ∞ Φ₁.symm)
    (hΦ₁b : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ₁ x‖ ≤ C)
    (hΨ₁b : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ₁.symm x‖ ≤ C)
    (hΦ₂ : ContDiff ℝ ∞ Φ₂) (hΨ₂ : ContDiff ℝ ∞ Φ₂.symm)
    (hΦ₂b : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ₂ x‖ ≤ C)
    (hΨ₂b : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ₂.symm x‖ ≤ C)
    (h₁ : ContDiff ℝ ∞ (Φ₁.trans Φ₂)) (h₂ : ContDiff ℝ ∞ (Φ₁.trans Φ₂).symm)
    (hb₁ : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (Φ₁.trans Φ₂) x‖ ≤ C)
    (hb₂ : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (Φ₁.trans Φ₂).symm x‖ ≤ C) :
    compCLEOfContDiff F φ s p q (Φ₁.trans Φ₂) h₁ h₂ hb₁ hb₂ =
      (compCLEOfContDiff F φ s p q Φ₂ hΦ₂ hΨ₂ hΦ₂b hΨ₂b).trans
        (compCLEOfContDiff F φ s p q Φ₁ hΦ₁ hΨ₁ hΦ₁b hΨ₁b) :=
  compCLE_trans _ _ _ _ _ _ _ _ _ _ _ _

/-- **The norm of the pullback by a smooth diffeomorphism.** There is `C`, depending only on `φ`,
`s` and `L`, with the following property. If the derivatives of `Φ` and of `Φ⁻¹` of orders `1` to
`⌊|s|⌋₊ + 2` are bounded by `L`, then the pullback along `Φ` and its inverse have operator norm at
most `C` on `B^s_{p,q}` for all `1 ≤ p, q ≤ ∞`. -/
theorem exists_norm_compCLEOfContDiff_le (φ : ContDiffBump (0 : E)) (s L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {Φ : E ≃ E}
      (hΦ : ContDiff ℝ ∞ Φ) (hΨ : ContDiff ℝ ∞ Φ.symm)
      (hΦb : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C)
      (hΨb : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C),
      (∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ L) →
      (∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ L) →
      ‖(compCLEOfContDiff F φ s p q Φ hΦ hΨ hΦb hΨb :
        BesovSpace F φ s p q →L[ℂ] BesovSpace F φ s p q)‖ ≤ C ∧
      ‖((compCLEOfContDiff F φ s p q Φ hΦ hΨ hΦb hΨb).symm :
        BesovSpace F φ s p q →L[ℂ] BesovSpace F φ s p q)‖ ≤ C := by
  obtain ⟨C, hC, hnorm⟩ := exists_norm_compCLE_le (F := F) φ s L
  refine ⟨C, hC, fun {p q} _ _ Φ hΦ hΨ hΦb hΨb hΦL hΨL ↦ ⟨hnorm _ _ _ _ hΦL hΨL, ?_⟩⟩
  rw [compCLEOfContDiff_symm]
  exact hnorm _ _ _ _ hΨL hΦL

/-! ### Translations and continuous linear automorphisms -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
private theorem compCLM_congr_equiv {Φ₁ Φ₂ : E ≃ E} (h : Φ₁ = Φ₂)
    (hΦ₁ : (Φ₁ : E → E).HasTemperateGrowth) (hΨ₁ : (Φ₁.symm : E → E).HasTemperateGrowth)
    (hΦ₂ : (Φ₂ : E → E).HasTemperateGrowth) (hΨ₂ : (Φ₂.symm : E → E).HasTemperateGrowth) :
    TemperedDistribution.compCLM F Φ₁ hΦ₁ hΨ₁ = TemperedDistribution.compCLM F Φ₂ hΦ₂ hΨ₂ := by
  subst h
  rfl

variable (F φ s p q) in
/-- **Translation on Besov spaces.** Translating by `a ∈ E`, `u ↦ u(· + a)`, is an isomorphism of
`B^s_{p,q}` whose operator norm is bounded uniformly in `a`, `p` and `q`
(`TauCeti.BesovSpace.exists_norm_translateEquiv_le`). -/
def translateEquiv (a : E) : BesovSpace F φ s p q ≃L[ℂ] BesovSpace F φ s p q :=
  compCLE F φ s p q (Equiv.addRight a)
    (by dsimp only [Equiv.coe_addRight]; fun_prop)
    (by dsimp only [Equiv.addRight_symm_apply]; fun_prop)
    (fun _ hn _ ↦ ⟨1, norm_iteratedFDeriv_addRight_le a hn⟩)
    (fun _ hn _ ↦ ⟨1, norm_iteratedFDeriv_addRight_le (-a) hn⟩)

@[simp]
theorem toDistr_translateEquiv (a : E) (u : BesovSpace F φ s p q) :
    (translateEquiv F φ s p q a u).toDistr =
      TemperedDistribution.compCLM F (Equiv.addRight a)
        (by dsimp only [Equiv.coe_addRight]; fun_prop)
        (by dsimp only [Equiv.addRight_symm_apply]; fun_prop) u.toDistr := by
  rw [translateEquiv, toDistr_compCLE]

@[simp]
theorem translateEquiv_zero :
    translateEquiv F φ s p q (0 : E) = ContinuousLinearEquiv.refl ℂ _ := by
  ext u : 3
  have h := DFunLike.congr_fun (compCLM_congr_equiv (F := F)
    (Φ₁ := Equiv.addRight (0 : E)) (Φ₂ := Equiv.refl E) (by ext x; simp)
    (by dsimp only [Equiv.coe_addRight]; fun_prop)
    (by dsimp only [Equiv.addRight_symm_apply]; fun_prop) .id .id) u.toDistr
  exact (toDistr_translateEquiv 0 u).trans
    (h.trans (DFunLike.congr_fun (TemperedDistribution.compCLM_refl .id .id) u.toDistr))

@[simp]
theorem translateEquiv_symm (a : E) :
    (translateEquiv F φ s p q a).symm = translateEquiv F φ s p q (-a) := by
  ext u : 3
  rw [translateEquiv, compCLE_symm, toDistr_compCLE, toDistr_translateEquiv,
    compCLM_congr_equiv (Equiv.addRight_symm a)]

theorem translateEquiv_add (a b : E) :
    translateEquiv F φ s p q (a + b) =
      (translateEquiv F φ s p q b).trans (translateEquiv F φ s p q a) := by
  ext u : 3
  have hab : Equiv.addRight (a + b) = (Equiv.addRight a).trans (Equiv.addRight b) := by
    ext x; simp [add_assoc]
  have h₁ : ((Equiv.addRight a).trans (Equiv.addRight b) : E → E).HasTemperateGrowth := by
    rw [← hab, Equiv.coe_addRight]; fun_prop
  have h₂ : (((Equiv.addRight a).trans (Equiv.addRight b)).symm : E → E).HasTemperateGrowth := by
    rw [← hab, Equiv.addRight_symm, Equiv.coe_addRight]; fun_prop
  rw [ContinuousLinearEquiv.trans_apply, toDistr_translateEquiv, toDistr_translateEquiv,
    toDistr_translateEquiv, compCLM_congr_equiv hab _ _ h₁ h₂,
    TemperedDistribution.compCLM_trans, ContinuousLinearMap.comp_apply]

/-- **Uniform translation invariance of Besov norms.** There is `C`, depending only on `φ` and
`s`, such that translation by any `a ∈ E` has operator norm at most `C` on `B^s_{p,q}` for all
`1 ≤ p, q ≤ ∞`. -/
theorem exists_norm_translateEquiv_le (φ : ContDiffBump (0 : E)) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (a : E),
      ‖(translateEquiv F φ s p q a : BesovSpace F φ s p q →L[ℂ] BesovSpace F φ s p q)‖ ≤ C := by
  obtain ⟨C, hC, hnorm⟩ := exists_norm_compCLE_le (F := F) φ s 1
  exact ⟨C, hC, fun {p q} _ _ a ↦ hnorm _ _ _ _
    (fun _ hn _ x ↦ norm_iteratedFDeriv_addRight_le a hn x)
    (fun _ hn _ x ↦ norm_iteratedFDeriv_addRight_le (-a) hn x)⟩

variable (F φ s p q) in
/-- **Pullback along a continuous linear automorphism** `e` of `E`, as an isomorphism of
`B^s_{p,q}`. -/
def compContinuousLinearEquiv (e : E ≃L[ℝ] E) :
    BesovSpace F φ s p q ≃L[ℂ] BesovSpace F φ s p q :=
  compCLE F φ s p q e.toEquiv e.hasTemperateGrowth e.symm.hasTemperateGrowth
    (fun _ hn _ ↦ ⟨‖(e : E →L[ℝ] E)‖, (e : E →L[ℝ] E).norm_iteratedFDeriv_le_norm hn⟩)
    (fun _ hn _ ↦ ⟨‖(e.symm : E →L[ℝ] E)‖, (e.symm : E →L[ℝ] E).norm_iteratedFDeriv_le_norm hn⟩)

@[simp]
theorem toDistr_compContinuousLinearEquiv (e : E ≃L[ℝ] E) (u : BesovSpace F φ s p q) :
    (compContinuousLinearEquiv F φ s p q e u).toDistr =
      TemperedDistribution.compCLM F e.toEquiv e.hasTemperateGrowth e.symm.hasTemperateGrowth
        u.toDistr :=
  toDistr_compCLE u

@[simp]
theorem compContinuousLinearEquiv_symm (e : E ≃L[ℝ] E) :
    (compContinuousLinearEquiv F φ s p q e).symm = compContinuousLinearEquiv F φ s p q e.symm :=
  compCLE_symm

@[simp]
theorem compContinuousLinearEquiv_refl :
    compContinuousLinearEquiv F φ s p q (ContinuousLinearEquiv.refl ℝ E) =
      ContinuousLinearEquiv.refl ℂ _ := by
  ext u : 3
  have h := DFunLike.congr_fun (compCLM_congr_equiv (F := F)
    (Φ₁ := (ContinuousLinearEquiv.refl ℝ E).toEquiv) (Φ₂ := Equiv.refl E) rfl
    (ContinuousLinearEquiv.refl ℝ E).hasTemperateGrowth
    (ContinuousLinearEquiv.refl ℝ E).symm.hasTemperateGrowth .id .id) u.toDistr
  exact (toDistr_compContinuousLinearEquiv _ u).trans
    (h.trans (DFunLike.congr_fun (TemperedDistribution.compCLM_refl .id .id) u.toDistr))

theorem compContinuousLinearEquiv_trans (e₁ e₂ : E ≃L[ℝ] E) :
    compContinuousLinearEquiv F φ s p q (e₁.trans e₂) =
      (compContinuousLinearEquiv F φ s p q e₂).trans (compContinuousLinearEquiv F φ s p q e₁) := by
  ext u : 3
  rw [ContinuousLinearEquiv.trans_apply, toDistr_compContinuousLinearEquiv,
    toDistr_compContinuousLinearEquiv, toDistr_compContinuousLinearEquiv]
  exact DFunLike.congr_fun (TemperedDistribution.compCLM_trans
    (φ := e₁.toEquiv) (χ := e₂.toEquiv)
    e₁.hasTemperateGrowth e₁.symm.hasTemperateGrowth
    e₂.hasTemperateGrowth e₂.symm.hasTemperateGrowth
    (e₁.trans e₂).hasTemperateGrowth (e₁.trans e₂).symm.hasTemperateGrowth) u.toDistr

end TauCeti.BesovSpace
