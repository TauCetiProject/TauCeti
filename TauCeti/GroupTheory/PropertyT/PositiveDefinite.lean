/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import TauCeti.GroupTheory.PropertyT.KazhdanPair
public import TauCeti.RepresentationTheory.Continuous.Unitary.PositiveDefinite
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import TauCeti.Analysis.InnerProductSpace.UnitVector
import TauCeti.Analysis.PositiveDefinite.Kernel.Bounds
import TauCeti.Analysis.PositiveDefinite.Kernel.Schoenberg
import TauCeti.Analysis.RCLike.Basic
import TauCeti.GroupTheory.PositiveDefinite.Metric
import TauCeti.RepresentationTheory.Continuous.Unitary.OrbitConvexHull

/-!
# Quantitative and positive-definite characterizations of relative property (T)

This file establishes the quantitative invariant-vector and positive-definite characterizations of
relative property (T) for a subgroup `Λ` of a discrete group `Γ`:

* For an arbitrary subgroup `Λ` of any discrete group `Γ`, quantitative positive-definite
  approximation or net uniform convergence implies relative property (T) in every universe. For a
  normal subgroup `Λ`, quantitative Kazhdan approximation
  (`IsKazhdanPair.exists_mem_invariants_norm_sub_lt`) yields the converse without countability in
  the universe `v` of `Γ`.
* For an arbitrary subgroup `Λ` of a countable discrete group `Γ`, relative property (T) in any
  universe `u` is equivalent to:
  1. **Quantitative invariant-vector approximation**: for every `ε > 0`, there exist a finite set
     `F ⊆ Γ` and `δ > 0` such that every `(F, δ)`-invariant unit vector of a unitary representation
     is within `ε` of a `Λ`-invariant vector;
  2. **Quantitative positive-definite approximation**: for every `ε > 0`, there exist a finite set
     `F ⊆ Γ` and `δ > 0` such that every normalized positive-definite function `φ : Γ → ℂ` within
     `δ` of `1` on `F` is within `ε` of `1` on all of `Λ`;
  3. **Uniform convergence on `Λ`**: every net (or sequence) of normalized positive-definite
     functions converging pointwise to `1` on `Γ` converges uniformly to `1` on `Λ`.

When `Λ` is not normal, `(H^Λ)ᗮ` need not be `Γ`-invariant and the finite set `F` in the
quantitative approximation must depend on `ε`. Following Jolissaint and Anantharaman–Popa, if
uniform convergence on `Λ` fails along an exhausting sequence of finite subsets of a countable
group `Γ`, one exponentiates a weighted infinite sum `∑' k, (k + 1) * (1 - φ k g)` to obtain a
normalized positive-definite function `Φ = exp (-t * ψ)` whose GNS representation has an
`(F₀, δ₀)`-invariant unit vector, hence a nonzero `Λ`-invariant vector, contradicting the decay of
`Φ (a⁻¹ * hₙ * b)` along the bad elements `hₙ ∈ Λ`.

## Main statements

* `Subgroup.RelativePropertyT.exists_forall_norm_sub_one_lt`,
  `Subgroup.RelativePropertyT.tendstoUniformlyOn`,
  `Subgroup.relativePropertyT_iff_forall_exists_forall_norm_sub_one_lt`, and
  `Subgroup.relativePropertyT_iff_forall_tendstoUniformlyOn`: positive-definite characterizations
  for normal subgroups without countability.
* `Subgroup.relativePropertyT_of_exists_forall_norm_sub_one_lt` and
  `Subgroup.relativePropertyT_of_forall_tendstoUniformlyOn`: sufficient conditions for arbitrary
  subgroups and universes.
* `Subgroup.relativePropertyT_iff_forall_exists_invariant_norm_sub_lt`: quantitative
  `Λ`-invariant vector characterization for countable groups.
* `Subgroup.relativePropertyT_iff_forall_posSemidef_norm_sub_one_lt`: quantitative
  positive-definite characterization for countable groups.
* `Subgroup.RelativePropertyT.tendstoUniformlyOn_of_countable`,
  `Subgroup.relativePropertyT_iff_tendstoUniformlyOn_nat`, and
  `Subgroup.relativePropertyT_iff_tendstoUniformlyOn`: uniform convergence of normalized
  positive-definite functions on `Λ` for countable groups.

## References

* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Proposition 14.1.2.
* P. Jolissaint, *On property (T) for pairs of topological groups*, Enseign. Math. (2) 51 (2005),
  31–45, Theorem 1.2.
* B. Bekka, P. de la Harpe and A. Valette, *Kazhdan's Property (T)*, Proposition 1.1.9 and
  Appendix C.5.
-/

public section

namespace Subgroup

universe u v w

open ContRepresentation Filter Topology
open scoped ComplexConjugate ComplexOrder InnerProductSpace

variable {Γ : Type v} [Group Γ]

/-! ### Equivalence bridges between invariant vectors and positive-definite functions -/

section Bridges

/-- Internal shorthand for the quantitative positive-definite approximation property on `Λ`. -/
private def PosSemidefApprox (Λ : Subgroup Γ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ (F : Finset Γ) (δ : ℝ), 0 < δ ∧
      ∀ φ : Γ → ℂ, (Matrix.of fun a b : Γ ↦ φ (a⁻¹ * b)).PosSemidef → φ 1 = 1 →
        (∀ g ∈ F, ‖φ g - 1‖ < δ) → ∀ h ∈ Λ, ‖φ h - 1‖ < ε

/-- Quantitative positive-definite approximation on `Λ` yields `ε`-close `Λ`-invariant vectors in
every Hilbert-space universe `u`, via the Alaoglu–Birkhoff orbit projection. -/
private theorem approx_invariant_of_posSemidef_approx {Λ : Subgroup Γ}
    (hpd_approx : PosSemidefApprox Λ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : Finset Γ) (δ : ℝ), 0 < δ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (ρ : ContRepresentation ℂ Γ H), ρ.IsUnitary →
          ∀ ξ : H, ‖ξ‖ = 1 → (∀ g ∈ F, ‖ρ g ξ - ξ‖ < δ) →
            ∃ v ∈ (ρ.restrict Λ.subtype).invariants, ‖v - ξ‖ < ε := by
  obtain ⟨F, δ, hδ, hFδ⟩ := hpd_approx (ε ^ 2 / 4) (by positivity)
  refine ⟨F, δ, hδ, fun H _ _ _ ρ hρ ξ hξ hξF ↦ ?_⟩
  let φ : Γ → ℂ := fun g ↦ ⟪ξ, ρ g ξ⟫_ℂ
  have hφ : (Matrix.of fun a b : Γ ↦ φ (a⁻¹ * b)).PosSemidef :=
    hρ.posSemidef_inner_map_inv_mul ξ
  have hξ_inner : ⟪ξ, ξ⟫_ℂ = 1 := inner_self_eq_one_of_norm_eq_one (𝕜 := ℂ) hξ
  have hφ1 : φ 1 = 1 := by
    dsimp only [φ]
    rw [map_one, one_apply_eq_self, hξ_inner]
  have hφF (g : Γ) (hg : g ∈ F) : ‖φ g - 1‖ < δ :=
    (TauCeti.norm_inner_sub_one_le hξ _).trans_lt (hξF g hg)
  have horb (k : Λ) : ‖(ρ.restrict Λ.subtype) k ξ - ξ‖ ≤ (3 / 4 : ℝ) * ε := by
    have hk := hFδ φ hφ hφ1 hφF k k.property
    have hre : 1 - (φ k).re < ε ^ 2 / 4 :=
      (RCLike.one_sub_re_le_norm_sub_one (φ k)).trans_lt hk
    have hsq : ‖ρ k ξ - ξ‖ ^ 2 = 2 * (1 - (φ k).re) := by
      rw [@norm_sub_sq ℂ, hρ.norm_map, hξ, one_pow]
      have hsymm : RCLike.re ⟪ρ k ξ, ξ⟫_ℂ = (φ k).re :=
        inner_re_symm (𝕜 := ℂ) (ρ k ξ) ξ
      rw [hsymm]
      ring
    rw [restrict_apply_apply, Subgroup.coe_subtype]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (by nlinarith)
  obtain ⟨v, hv, hvξ⟩ := (hρ.restrict Λ.subtype).exists_invariant_norm_sub_le horb
  exact ⟨v, hv, hvξ.trans_lt (by linarith)⟩

/-- Quantitative positive-definite approximation on `Λ` implies uniform convergence on `Λ` along
any filter of normalized positive-definite functions converging pointwise to `1`. -/
private theorem tendstoUniformlyOn_of_posSemidef_approx {Λ : Subgroup Γ}
    (hpd_approx : PosSemidefApprox Λ) {ι : Type w} {l : Filter ι} {φ : ι → Γ → ℂ}
    (hpd : ∀ i, (Matrix.of fun a b : Γ ↦ φ i (a⁻¹ * b)).PosSemidef)
    (h1 : ∀ i, φ i 1 = 1) (hpt : ∀ g, Tendsto (fun i ↦ φ i g) l (𝓝 1)) :
    TendstoUniformlyOn φ 1 l Λ := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨F, δ, hδ, hFδ⟩ := hpd_approx ε hε
  have hev : ∀ᶠ i in l, ∀ g ∈ F, ‖φ i g - 1‖ < δ :=
    (Filter.eventually_all_finset F).mpr fun g _ ↦ by
      simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp (hpt g) δ hδ
  filter_upwards [hev] with i hi x hx
  simpa only [Pi.one_apply, dist_eq_norm', norm_sub_rev] using hFδ (φ i) (hpd i) (h1 i) hi x hx

/-- If quantitative positive-definite approximation fails on `Λ`, any exhaustion `(A i, δ i)` along
a nontrivial filter `l` of finite subsets of `Γ` and positive tolerances tending to `0` produces a
family of normalized positive-definite functions converging pointwise to `1` on `Γ` but not
uniformly on `Λ`. -/
private theorem posSemidef_approx_of_tendstoUniformlyOn_of_exhaustion {Λ : Subgroup Γ}
    {ι : Type w} {l : Filter ι} [l.NeBot]
    (A : ι → Finset Γ) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    (hA : ∀ g : Γ, ∀ᶠ i in l, g ∈ A i) (hδ0 : Tendsto δ l (𝓝 0))
    (hunif : ∀ φ : ι → Γ → ℂ,
      (∀ i, (Matrix.of fun a b : Γ ↦ φ i (a⁻¹ * b)).PosSemidef) →
        (∀ i, φ i 1 = 1) → (∀ g, Tendsto (fun i ↦ φ i g) l (𝓝 1)) →
          TendstoUniformlyOn φ 1 l Λ) :
    PosSemidefApprox Λ := by
  by_contra hnot
  unfold PosSemidefApprox at hnot
  push Not at hnot
  obtain ⟨ε₀, hε₀, hbad⟩ := hnot
  have hex (i : ι) := hbad (A i) (δ i) (hδ i)
  choose φ hpd h1 hF h hΛ hge using hex
  have hpt (g : Γ) : Tendsto (fun i : ι ↦ φ i g) l (𝓝 1) := by
    rw [Metric.tendsto_nhds]
    intro r hr
    have hδr : ∀ᶠ i in l, δ i < r := by
      filter_upwards [Metric.tendsto_nhds.mp hδ0 r hr] with i hi
      rw [dist_zero_right, Real.norm_of_nonneg (hδ i).le] at hi
      exact hi
    filter_upwards [hA g, hδr] with i hgi hri
    rw [dist_eq_norm]
    exact (hF i g hgi).trans hri
  have hu := Metric.tendstoUniformlyOn_iff.mp (hunif φ hpd h1 hpt) ε₀ hε₀
  obtain ⟨i, hi⟩ := hu.exists
  have hlt : ‖φ i (h i) - 1‖ < ε₀ := by
    simpa only [Pi.one_apply, dist_eq_norm, norm_sub_rev] using hi (h i) (hΛ i)
  exact (not_lt_of_ge (hge i)) hlt

/-- When `Γ` is countable, sequential uniform convergence on `Λ` already implies quantitative
positive-definite approximation on `Λ`. -/
private theorem posSemidef_approx_of_tendstoUniformlyOn_nat [Countable Γ] {Λ : Subgroup Γ}
    (hunif : ∀ φ : ℕ → Γ → ℂ,
      (∀ n, (Matrix.of fun a b : Γ ↦ φ n (a⁻¹ * b)).PosSemidef) →
        (∀ n, φ n 1 = 1) → (∀ g, Tendsto (fun n ↦ φ n g) atTop (𝓝 1)) →
          TendstoUniformlyOn φ 1 atTop Λ) :
    PosSemidefApprox Λ := by
  classical
  obtain ⟨A, -, hA⟩ := exists_seq_monotone_tendsto_atTop_atTop (Finset Γ)
  exact posSemidef_approx_of_tendstoUniformlyOn_of_exhaustion (l := atTop)
    A (fun n ↦ 1 / (n + 1 : ℝ)) (fun _ ↦ Nat.one_div_pos_of_nat)
    (fun g ↦ hA.eventually (eventually_finset_mem_atTop g))
    tendsto_one_div_add_atTop_nhds_zero_nat hunif

omit [Group Γ] in
/-- Summability of the weighted series `∑' k, (k + 1) * (1 - φ k g)` along an exhaustion of `Γ`. -/
private theorem summable_mul_one_sub_of_exhaustion {A : ℕ → Finset Γ}
    (hA : ∀ g : Γ, ∀ᶠ k in atTop, g ∈ A k) {φ : ℕ → Γ → ℂ}
    (hF : ∀ k, ∀ g ∈ A k, ‖φ k g - 1‖ ≤ 1 / ((k + 1 : ℝ) * (2 : ℝ) ^ (k + 1))) (g : Γ) :
    Summable fun k : ℕ ↦ ((k + 1 : ℝ) : ℂ) * (1 - φ k g) := by
  have hgeom : Summable fun k : ℕ ↦ ((1 / 2 : ℝ) ^ (k + 1)) :=
    (summable_geometric_two.mul_left (1 / 2)).congr fun k ↦ by ring
  refine Summable.of_norm_bounded_eventually_nat hgeom ?_
  filter_upwards [hA g] with k hmem
  have hlt := hF k g hmem
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_sub_rev]
  calc (k + 1 : ℝ) * ‖φ k g - 1‖
      ≤ (k + 1 : ℝ) * (1 / ((k + 1 : ℝ) * (2 : ℝ) ^ (k + 1))) := by gcongr
    _ = (1 / 2 : ℝ) ^ (k + 1) := by
        rw [one_div, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul, ← inv_pow,
          ← one_div]

/-- Double-translate separation bound for the Jolissaint–Anantharaman–Popa step: if a normalized
positive-definite function `φ : Γ → ℂ` satisfies `‖φ a - 1‖ ≤ ε ^ 2 / 32`,
`‖φ b - 1‖ ≤ ε ^ 2 / 32`, and `ε ≤ ‖φ g - 1‖` with `0 ≤ ε`, then
`ε ^ 2 / 8 ≤ 1 - (φ (a⁻¹ * g * b)).re`. -/
private theorem sq_div_eight_le_one_sub_re_inv_mul_mul {φ : Γ → ℂ}
    (hφ : (Matrix.of fun x y : Γ ↦ φ (x⁻¹ * y)).PosSemidef) (h1 : φ 1 = 1)
    {a g b : Γ} {ε : ℝ} (hε : 0 ≤ ε)
    (ha : ‖φ a - 1‖ ≤ ε ^ 2 / 32) (hb : ‖φ b - 1‖ ≤ ε ^ 2 / 32)
    (hg : ε ≤ ‖φ g - 1‖) :
    ε ^ 2 / 8 ≤ 1 - (φ (a⁻¹ * g * b)).re := by
  let u : ℝ := Real.sqrt (ε ^ 2 / 32)
  have hu2 : u ^ 2 = ε ^ 2 / 32 := Real.sq_sqrt (by positivity)
  have htri := hφ.le_sqrt_re_one_sub_re_inv_mul_mul a g b
  simp only [RCLike.re_to_complex, h1, Complex.one_re] at htri
  have hre_a : 1 - (φ a).re ≤ ε ^ 2 / 32 :=
    (RCLike.one_sub_re_le_norm_sub_one (φ a)).trans ha
  have hre_b : 1 - (φ b).re ≤ ε ^ 2 / 32 :=
    (RCLike.one_sub_re_le_norm_sub_one (φ b)).trans hb
  have hsq_g : (4 * u) ^ 2 ≤ 1 - (φ g).re := by
    have hnorm : ‖φ g - 1‖ ^ 2 ≤ 2 * (1 - (φ g).re) := hφ.norm_sub_one_sq_le h1 g
    have hε_sq : ε ^ 2 ≤ ‖φ g - 1‖ ^ 2 := pow_le_pow_left₀ hε hg 2
    nlinarith
  have hsqrt_g : 4 * u ≤ Real.sqrt (1 - (φ g).re) := Real.le_sqrt_of_sq_le hsq_g
  have hsqrt_a : Real.sqrt (1 - (φ a).re) ≤ u := Real.sqrt_le_sqrt hre_a
  have hsqrt_b : Real.sqrt (1 - (φ b).re) ≤ u := Real.sqrt_le_sqrt hre_b
  have hsqrt_mid : 2 * u ≤ Real.sqrt (1 - (φ (a⁻¹ * g * b)).re) := by linarith
  have hsq_mid : (2 * u) ^ 2 ≤ (Real.sqrt (1 - (φ (a⁻¹ * g * b)).re)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsqrt_mid 2
  rw [Real.sq_sqrt (by simpa using hφ.one_sub_re_nonneg h1 _)] at hsq_mid
  nlinarith

/-- Exponential decay of double translates `Φ (a⁻¹ * s n * b)` along the bad sequence `s`. -/
private theorem tendsto_cexp_neg_tsum_mul_zero {A : ℕ → Finset Γ}
    (hA : ∀ g : Γ, ∀ᶠ k in atTop, g ∈ A k)
    {φ : ℕ → Γ → ℂ} (hpd : ∀ k, (Matrix.of fun a b : Γ ↦ φ k (a⁻¹ * b)).PosSemidef)
    (h1 : ∀ k, φ k 1 = 1)
    (hsumm : ∀ g, Summable fun k : ℕ ↦ ((k + 1 : ℝ) : ℂ) * (1 - φ k g))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hF : ∀ k, ∀ g ∈ A k, ‖φ k g - 1‖ < ε₀ ^ 2 / 32)
    {s : ℕ → Γ} (hsε : ∀ k, ε₀ ≤ ‖φ k (s k) - 1‖) {t : ℝ} (ht : 0 < t) (a b : Γ) :
    Tendsto (fun n ↦ Complex.exp (-(t : ℂ) *
      ∑' k : ℕ, ((k + 1 : ℝ) : ℂ) * (1 - φ k (a⁻¹ * s n * b)))) atTop (𝓝 0) := by
  let ψ (g : Γ) : ℂ := ∑' k : ℕ, ((k + 1 : ℝ) : ℂ) * (1 - φ k g)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖Complex.exp (-(t : ℂ) * ψ (a⁻¹ * s n * b))‖ ≤
        Real.exp (-(t * (ε₀ ^ 2 / 8)) * (n + 1 : ℝ)) := by
    filter_upwards [hA a, hA b] with n ha_mem hb_mem
    have hre_ge : ε₀ ^ 2 / 8 ≤ 1 - (φ n (a⁻¹ * s n * b)).re :=
      sq_div_eight_le_one_sub_re_inv_mul_mul (hpd n) (h1 n) hε₀.le
        (hF n a ha_mem).le (hF n b hb_mem).le (hsε n)
    have hsumm_re : Summable fun k : ℕ ↦ (k + 1 : ℝ) * (1 - (φ k (a⁻¹ * s n * b)).re) := by
      simpa using Complex.reCLM.summable (hsumm (a⁻¹ * s n * b))
    have hψ_re : (ψ (a⁻¹ * s n * b)).re =
        ∑' k : ℕ, (k + 1 : ℝ) * (1 - (φ k (a⁻¹ * s n * b)).re) := by
      simpa [ψ] using Complex.reCLM.map_tsum (hsumm (a⁻¹ * s n * b))
    have htsum_ge : (n + 1 : ℝ) * (ε₀ ^ 2 / 8) ≤ (ψ (a⁻¹ * s n * b)).re := by
      rw [hψ_re]
      exact (mul_le_mul_of_nonneg_left hre_ge (by positivity)).trans <|
        hsumm_re.le_tsum n fun k _ ↦ mul_nonneg (by positivity)
          ((hpd k).one_sub_re_nonneg (h1 k) _)
    rw [Complex.norm_exp, show (-(t : ℂ) * ψ (a⁻¹ * s n * b)).re =
        -t * (ψ (a⁻¹ * s n * b)).re by simp]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hexp0 : Tendsto (fun n : ℕ ↦ Real.exp (-(t * (ε₀ ^ 2 / 8)) * (n + 1 : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp <|
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop_of_neg
        (by nlinarith [sq_pos_of_pos hε₀])
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) hbound hexp0

/-- Positive semidefiniteness of `g ↦ exp (-t * ∑' k, w k * (1 - φ k g))` for nonnegative
weights `w` and positive-definite functions `φ k`, via `CondNegSemidef.tsum_of_summable` and
Schoenberg's theorem. -/
private theorem posSemidef_cexp_neg_tsum_mul {φ : ℕ → Γ → ℂ}
    (hpd : ∀ k, (Matrix.of fun a b : Γ ↦ φ k (a⁻¹ * b)).PosSemidef)
    {w : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k)
    (hsumm : ∀ g, Summable fun k : ℕ ↦ (w k : ℂ) * (1 - φ k g))
    {t : ℝ} (ht : 0 ≤ t) :
    (Matrix.of fun a b : Γ ↦
      Complex.exp (-(t : ℂ) * ∑' k : ℕ, (w k : ℂ) * (1 - φ k (a⁻¹ * b)))).PosSemidef := by
  let Ψ : Matrix Γ Γ ℂ :=
    Matrix.of fun a b : Γ ↦ ∑' k : ℕ, (w k : ℂ) * (1 - φ k (a⁻¹ * b))
  have hΨ : Ψ.CondNegSemidef := by
    refine Matrix.CondNegSemidef.tsum_of_summable
      (f := fun (k : ℕ) (a b : Γ) ↦ (w k : ℂ) * (1 - φ k (a⁻¹ * b)))
      (fun a b ↦ hsumm (a⁻¹ * b)) fun k ↦ ?_
    convert ((hpd k).const_sub_condNegSemidef (star_one ℂ)).smul
      (a := (w k : ℂ)) (by exact_mod_cast hw k) using 1
    ext a b
    simp
  simpa [Ψ] using hΨ.posSemidef_cexp_neg_mul ht

omit [Group Γ] in
/-- For a finite set `F₀` and `ε > 0`, there exists `t > 0` such that `exp (-t * ψ g)` lies within
`ε` of `1` on `F₀`. -/
private theorem exists_pos_forall_mem_norm_cexp_neg_mul_sub_lt (F₀ : Finset Γ) (ψ : Γ → ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ ∀ g ∈ F₀, ‖Complex.exp (-(t : ℂ) * ψ g) - 1‖ < ε := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ g ∈ F₀, ‖Complex.exp (-(t : ℂ) * ψ g) - 1‖ < ε := by
    refine (Filter.eventually_all_finset F₀).mpr fun g _ ↦ ?_
    have hcont : Continuous fun t : ℝ ↦ Complex.exp (-(t : ℂ) * ψ g) := by fun_prop
    have ht0 : Tendsto (fun t : ℝ ↦ Complex.exp (-(t : ℂ) * ψ g)) (𝓝 0) (𝓝 1) := by
      simpa using (hcont.continuousAt (x := 0)).tendsto
    simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp ht0 ε hε
  obtain ⟨r, hr, hr_sub⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨r / 2, half_pos hr, hr_sub ?_⟩
  rw [Metric.mem_ball, dist_zero_right, Real.norm_of_nonneg (half_pos hr).le]
  exact half_lt_self hr

/-- **Jolissaint – Anantharaman–Popa exponential step.** For a subgroup `Λ` of a countable group
`Γ`, relative property (T) implies quantitative positive-definite approximation on `Λ`. -/
private theorem posSemidef_approx_of_relativePropertyT [Countable Γ] {Λ : Subgroup Γ}
    (hΛ : Λ.RelativePropertyT.{v}) : PosSemidefApprox Λ := by
  classical
  -- Fix a Kazhdan pair `(F₀, δ₀)` and assume positive-definite approximation fails at scale `ε₀`.
  obtain ⟨F₀, δ₀, hδ₀, hK⟩ := Λ.relativePropertyT_iff_exists_isKazhdanPair.{v, v}.mp hΛ
  by_contra hnot
  unfold PosSemidefApprox at hnot
  push Not at hnot
  obtain ⟨ε₀, hε₀, hbad⟩ := hnot
  -- Exhaust `Γ` by finite sets `A k ⊇ F₀` to pick a bad sequence `(φ k, s k ∈ Λ)` violating `ε₀`.
  obtain ⟨B, -, hB⟩ := exists_seq_monotone_tendsto_atTop_atTop (Finset Γ)
  let A (k : ℕ) : Finset Γ := F₀ ∪ B k
  let η (k : ℕ) : ℝ := min (1 / ((k + 1 : ℝ) * (2 : ℝ) ^ (k + 1))) (ε₀ ^ 2 / 32)
  have hex (k : ℕ) := hbad (A k) (η k) (by positivity)
  choose φ hpd h1 hF s hsΛ hsε using hex
  have hA_mem (g : Γ) : ∀ᶠ k in atTop, g ∈ A k :=
    (hB.eventually (eventually_finset_mem_atTop g)).mono fun _ hg ↦ Finset.mem_union_right _ hg
  -- Define the weighted series `ψ g = ∑' k, (k + 1) * (1 - φ k g)`.
  have hsumm (g : Γ) : Summable fun k : ℕ ↦ ((k + 1 : ℝ) : ℂ) * (1 - φ k g) :=
    summable_mul_one_sub_of_exhaustion hA_mem
      (fun k x hx ↦ (hF k x hx).le.trans (min_le_left _ _)) g
  let ψ (g : Γ) : ℂ := ∑' k : ℕ, ((k + 1 : ℝ) : ℂ) * (1 - φ k g)
  -- Choose `t > 0` small enough that `Φ = exp (-t * ψ)` is `(F₀, δ₀ ^ 2 / 2)`-close to `1`.
  obtain ⟨t, ht, htF₀⟩ := exists_pos_forall_mem_norm_cexp_neg_mul_sub_lt F₀ ψ (by positivity :
    0 < δ₀ ^ 2 / 2)
  let Φ (g : Γ) : ℂ := Complex.exp (-(t : ℂ) * ψ g)
  have hΦ : (Matrix.of fun a b : Γ ↦ Φ (a⁻¹ * b)).PosSemidef :=
    posSemidef_cexp_neg_tsum_mul hpd (fun k ↦ by positivity) hsumm ht.le
  have hΦ1 : Φ 1 = 1 := by simp [Φ, ψ, h1]
  -- Its GNS vector `gnsVector 1` is `(F₀, δ₀)`-invariant, giving a nonzero `Λ`-invariant `v`.
  obtain ⟨v, hv0, hvΛ⟩ := (isKazhdanPair_def Λ F₀ δ₀).mp hK
    hΦ.gnsSpace hΦ.gnsRepresentation hΦ.isUnitary_gnsRepresentation
    ⟨hΦ.gnsVector 1, hΦ.norm_gnsVector_eq_one hΦ1 1,
      fun g hg ↦ hΦ.norm_gnsRepresentation_gnsVector_one_sub_lt hΦ1 hδ₀ (htF₀ g hg)⟩
  -- Exponential decay of `Φ (a⁻¹ * s n * b)` along `s n` forces `invariants = ⊥`, contradiction.
  have hbot : (hΦ.gnsRepresentation.restrict Λ.subtype).invariants = ⊥ :=
    hΦ.invariants_restrict_gnsRepresentation_eq_bot Λ.subtype (s := fun n ↦ ⟨s n, hsΛ n⟩)
      (tendsto_cexp_neg_tsum_mul_zero hA_mem hpd h1 hsumm hε₀
        (fun k x hx ↦ (hF k x hx).trans_le (min_le_right _ _)) hsε ht)
  exact hv0 ((Submodule.mem_bot ℂ).mp (hbot ▸ hvΛ))

end Bridges

/-! ### Main characterizations of relative property (T) -/

section

variable {Λ : Subgroup Γ}

/-- **Relative property (T) by positive-definite functions, uniform form.** If a normal subgroup
`Λ` has relative property (T), then for every `ε > 0` there are a finite set `F` and a `δ > 0` such
that every positive-definite function `φ` with `φ 1 = 1` and `‖φ g - 1‖ < δ` for `g ∈ F` satisfies
`‖φ h - 1‖ < ε` for every `h ∈ Λ`. -/
theorem RelativePropertyT.exists_forall_norm_sub_one_lt [Λ.Normal]
    (hΛ : Λ.RelativePropertyT.{v}) {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : Finset Γ) (δ : ℝ), 0 < δ ∧ ∀ φ : Γ → ℂ,
      (Matrix.of fun g h ↦ φ (g⁻¹ * h)).PosSemidef → φ 1 = 1 →
        (∀ g ∈ F, ‖φ g - 1‖ < δ) → ∀ h ∈ Λ, ‖φ h - 1‖ < ε := by
  obtain ⟨F, δ, hδ, hK⟩ := hΛ.exists_mem_invariants_norm_sub_lt.{v, v} (half_pos hε)
  refine ⟨F, δ ^ 2 / 2, by positivity, fun φ hφ hφ1 hφF h hh ↦ ?_⟩
  set π := hφ.gnsRepresentation
  set ξ := hφ.gnsVector 1
  have hπ : π.IsUnitary := hφ.isUnitary_gnsRepresentation
  -- The GNS vector at the identity is moved by less than `δ` by each element of `F`, so it lies
  -- within `ε / 2` of a `Λ`-invariant vector `η`.
  obtain ⟨η, hη, hξη⟩ := hK hφ.gnsSpace π hπ ξ fun g hg ↦ (sq_lt_sq₀ (norm_nonneg _) hδ.le).mp <|
    (hφ.norm_gnsRepresentation_gnsVector_one_sub_sq_le hφ1 g).trans_lt (by linarith [hφF g hg])
  -- Hence `h ∈ Λ` moves `ξ` by at most `2 * ‖ξ - η‖ < ε`.
  have hπη : π h η = η := (mem_invariants_restrict.mp hη) h hh
  have hmove : ‖π h ξ - ξ‖ ≤ 2 * ‖ξ - η‖ := by
    calc ‖π h ξ - ξ‖ = ‖π h (ξ - η) - (ξ - η)‖ := by rw [map_sub, hπη]; abel_nf
      _ ≤ ‖π h (ξ - η)‖ + ‖ξ - η‖ := norm_sub_le _ _
      _ = 2 * ‖ξ - η‖ := by rw [hπ.norm_map]; ring
  calc ‖φ h - 1‖ = ‖⟪ξ, π h ξ⟫_ℂ - 1‖ := by rw [hφ.inner_gnsVector_one_gnsRepresentation]
    _ ≤ ‖π h ξ - ξ‖ := TauCeti.norm_inner_sub_one_le (hφ.norm_gnsVector_one hφ1) _
    _ < ε := by linarith

/-- **Relative property (T) by positive-definite functions.** If a normal subgroup `Λ` has relative
property (T), then every net of positive-definite functions `φᵢ` with `φᵢ 1 = 1` converging
pointwise to `1` converges to `1` uniformly on `Λ`. -/
theorem RelativePropertyT.tendstoUniformlyOn [Λ.Normal] (hΛ : Λ.RelativePropertyT.{v})
    {ι : Type*} {l : Filter ι} {φ : ι → Γ → ℂ}
    (hφ : ∀ i, (Matrix.of fun g h ↦ φ i (g⁻¹ * h)).PosSemidef) (hφ1 : ∀ i, φ i 1 = 1)
    (hlim : ∀ g, Tendsto (fun i ↦ φ i g) l (𝓝 1)) :
    TendstoUniformlyOn φ (fun _ ↦ 1) l Λ :=
  tendstoUniformlyOn_of_posSemidef_approx
    (fun _ hε ↦ hΛ.exists_forall_norm_sub_one_lt hε) hφ hφ1 hlim

/-- **Relative property (T) from positive-definite functions, uniform form.** Let `ε < 1`. If there
are a finite set `F` and a `δ > 0` such that every positive-definite function `φ` with `φ 1 = 1`
and `‖φ g - 1‖ < δ` for `g ∈ F` satisfies `‖φ h - 1‖ < ε` for every `h ∈ Λ`, then `Λ` has relative
property (T), in every universe of representations. -/
theorem relativePropertyT_of_exists_forall_norm_sub_one_lt {ε : ℝ} (hε : ε < 1)
    (hΛ : ∃ (F : Finset Γ) (δ : ℝ), 0 < δ ∧ ∀ φ : Γ → ℂ,
      (Matrix.of fun g h ↦ φ (g⁻¹ * h)).PosSemidef → φ 1 = 1 →
        (∀ g ∈ F, ‖φ g - 1‖ < δ) → ∀ h ∈ Λ, ‖φ h - 1‖ < ε) :
    Λ.RelativePropertyT.{u} := by
  obtain ⟨F, δ, hδ, hF⟩ := hΛ
  refine (relativePropertyT_def Λ).mpr fun H _ _ _ ρ hρ hal ↦ ?_
  obtain ⟨ξ, hξ, hξF⟩ := (hasAlmostInvariantVectors_def ρ).mp hal F δ hδ
  -- The coefficient of `ξ` is a normalized positive-definite function close to `1` on `F`.
  have hclose := hF (fun g ↦ ⟪ξ, ρ g ξ⟫_ℂ) (hρ.posSemidef_inner_map_inv_mul ξ)
    (by simpa using inner_self_eq_one_of_norm_eq_one (𝕜 := ℂ) hξ)
    fun g hg ↦ (TauCeti.norm_inner_sub_one_le hξ _).trans_lt (hξF g hg)
  -- So its real part is at least `1 - ε > 0` on `Λ`.
  refine (hρ.restrict Λ.subtype).exists_ne_zero_mem_invariants_of_le_re_inner (ξ := ξ)
    (sub_pos.mpr hε) fun h ↦ ?_
  simp only [restrict_apply_apply, coe_subtype]
  linarith [hclose h h.property, RCLike.one_sub_re_le_norm_sub_one ⟪ξ, ρ h ξ⟫_ℂ]

/-- **Relative property (T) from positive-definite functions.** If every net of positive-definite
functions `φᵢ` with `φᵢ 1 = 1` converging pointwise to `1`, indexed by a type in the universe of
`Γ`, converges to `1` uniformly on `Λ`, then `Λ` has relative property (T), in every universe of
representations. -/
theorem relativePropertyT_of_forall_tendstoUniformlyOn
    (hΛ : ∀ (ι : Type v) (l : Filter ι) (φ : ι → Γ → ℂ),
      (∀ i, (Matrix.of fun g h ↦ φ i (g⁻¹ * h)).PosSemidef) → (∀ i, φ i 1 = 1) →
        (∀ g, Tendsto (fun i ↦ φ i g) l (𝓝 1)) → TendstoUniformlyOn φ (fun _ ↦ 1) l Λ) :
    Λ.RelativePropertyT.{u} := by
  classical
  exact relativePropertyT_of_exists_forall_norm_sub_one_lt (ε := 1 / 2) (by norm_num) <|
    posSemidef_approx_of_tendstoUniformlyOn_of_exhaustion (l := (atTop : Filter (Finset Γ × ℕ)))
      Prod.fst (fun i ↦ 1 / (i.2 + 1 : ℝ)) (fun _ ↦ Nat.one_div_pos_of_nat)
      (fun g ↦ (eventually_ge_atTop (({g}, 0) : Finset Γ × ℕ)).mono
        fun _ hi ↦ hi.1 (Finset.mem_singleton_self g))
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp
        (tendsto_atTop.mpr fun n ↦ eventually_atTop.mpr ⟨(∅, n), fun _ h ↦ h.2⟩))
      (hΛ _ atTop) (1 / 2) (by norm_num)

/-- **Relative property (T) by positive-definite functions, uniform form.** A normal subgroup `Λ`
has relative property (T) exactly when for every `ε > 0` there are a finite set `F` and a `δ > 0`
such that every positive-definite function `φ` with `φ 1 = 1` and `‖φ g - 1‖ < δ` for `g ∈ F`
satisfies `‖φ h - 1‖ < ε` for every `h ∈ Λ`. -/
theorem relativePropertyT_iff_forall_exists_forall_norm_sub_one_lt [Λ.Normal] :
    Λ.RelativePropertyT.{v} ↔ ∀ ε > 0, ∃ (F : Finset Γ) (δ : ℝ), 0 < δ ∧ ∀ φ : Γ → ℂ,
      (Matrix.of fun g h ↦ φ (g⁻¹ * h)).PosSemidef → φ 1 = 1 →
        (∀ g ∈ F, ‖φ g - 1‖ < δ) → ∀ h ∈ Λ, ‖φ h - 1‖ < ε :=
  ⟨fun hΛ _ hε ↦ hΛ.exists_forall_norm_sub_one_lt hε, fun h ↦
    relativePropertyT_of_exists_forall_norm_sub_one_lt (by norm_num) (h (1 / 2) (by norm_num))⟩

/-- **Relative property (T) by positive-definite functions.** A normal subgroup `Λ` has relative
property (T) exactly when every net of positive-definite functions `φᵢ` with `φᵢ 1 = 1` converging
pointwise to `1` converges to `1` uniformly on `Λ` (Anantharaman–Popa, Proposition 14.1.2). -/
theorem relativePropertyT_iff_forall_tendstoUniformlyOn [Λ.Normal] :
    Λ.RelativePropertyT.{v} ↔ ∀ (ι : Type v) (l : Filter ι) (φ : ι → Γ → ℂ),
      (∀ i, (Matrix.of fun g h ↦ φ i (g⁻¹ * h)).PosSemidef) → (∀ i, φ i 1 = 1) →
        (∀ g, Tendsto (fun i ↦ φ i g) l (𝓝 1)) → TendstoUniformlyOn φ (fun _ ↦ 1) l Λ :=
  ⟨fun hΛ _ _ _ hφ hφ1 hlim ↦ hΛ.tendstoUniformlyOn hφ hφ1 hlim,
    relativePropertyT_of_forall_tendstoUniformlyOn⟩

end

section Countable

variable [Countable Γ]

/-- **Quantitative invariant-vector characterization of relative property (T).** A subgroup `Λ` of
a countable discrete group `Γ` has relative property (T) if and only if for every `ε > 0` there is
a pair `(F, δ)` (`δ > 0`) such that every `(F, δ)`-invariant unit vector of a unitary
representation lies within `ε` of a `Λ`-invariant vector. -/
theorem relativePropertyT_iff_forall_exists_invariant_norm_sub_lt (Λ : Subgroup Γ) :
    Λ.RelativePropertyT.{u} ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ (F : Finset Γ) (δ : ℝ), 0 < δ ∧
          ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
            (ρ : ContRepresentation ℂ Γ H), ρ.IsUnitary →
              ∀ ξ : H, ‖ξ‖ = 1 → (∀ g ∈ F, ‖ρ g ξ - ξ‖ < δ) →
                ∃ v ∈ (ρ.restrict Λ.subtype).invariants, ‖v - ξ‖ < ε := by
  refine ⟨fun hΛ ε hε ↦ approx_invariant_of_posSemidef_approx
    (posSemidef_approx_of_relativePropertyT hΛ.of_universe) hε, fun hinv ↦ ?_⟩
  obtain ⟨F, δ, hδ, hF⟩ := hinv 1 zero_lt_one
  exact (isKazhdanPair_of_exists_invariant_norm_sub_lt_one hF).relativePropertyT hδ

/-- **Quantitative positive-definite characterization of relative property (T).** A subgroup `Λ` of
a countable discrete group `Γ` has relative property (T) if and only if for every `ε > 0` there is
a pair `(F, δ)` (`δ > 0`) such that every normalized positive-definite function within `δ` of `1`
on `F` is within `ε` of `1` on all of `Λ`. -/
theorem relativePropertyT_iff_forall_posSemidef_norm_sub_one_lt (Λ : Subgroup Γ) :
    Λ.RelativePropertyT.{u} ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ (F : Finset Γ) (δ : ℝ), 0 < δ ∧
          ∀ φ : Γ → ℂ, (Matrix.of fun a b : Γ ↦ φ (a⁻¹ * b)).PosSemidef → φ 1 = 1 →
            (∀ g ∈ F, ‖φ g - 1‖ < δ) → ∀ h ∈ Λ, ‖φ h - 1‖ < ε :=
  ⟨fun hΛ ↦ posSemidef_approx_of_relativePropertyT hΛ.of_universe, fun hpd_approx ↦
    relativePropertyT_of_exists_forall_norm_sub_one_lt (by norm_num)
      (hpd_approx (1 / 2) (by norm_num))⟩

/-- **Uniform convergence of positive-definite nets.** If a subgroup `Λ` of a countable discrete
group `Γ` has relative property (T), every filter of normalized positive-definite functions
converging pointwise to `1` on `Γ` converges uniformly to `1` on `Λ`. -/
theorem RelativePropertyT.tendstoUniformlyOn_of_countable {Λ : Subgroup Γ}
    (hΛ : Λ.RelativePropertyT.{u}) {ι : Type w} {l : Filter ι} {φ : ι → Γ → ℂ}
    (hpd : ∀ i, (Matrix.of fun a b : Γ ↦ φ i (a⁻¹ * b)).PosSemidef)
    (h1 : ∀ i, φ i 1 = 1) (hpt : ∀ g, Tendsto (fun i ↦ φ i g) l (𝓝 1)) :
    TendstoUniformlyOn φ 1 l Λ :=
  tendstoUniformlyOn_of_posSemidef_approx
    ((Λ.relativePropertyT_iff_forall_posSemidef_norm_sub_one_lt.{u}).mp hΛ) hpd h1 hpt

/-- **Sequential positive-definite characterization of relative property (T).** A subgroup `Λ` of a
countable discrete group `Γ` has relative property (T) if and only if every sequence of normalized
positive-definite functions converging pointwise to `1` on `Γ` converges uniformly to `1` on `Λ`. -/
theorem relativePropertyT_iff_tendstoUniformlyOn_nat (Λ : Subgroup Γ) :
    Λ.RelativePropertyT.{u} ↔
      ∀ φ : ℕ → Γ → ℂ,
        (∀ n, (Matrix.of fun a b : Γ ↦ φ n (a⁻¹ * b)).PosSemidef) →
          (∀ n, φ n 1 = 1) → (∀ g, Tendsto (fun n ↦ φ n g) atTop (𝓝 1)) →
            TendstoUniformlyOn φ 1 atTop Λ :=
  ⟨fun hΛ _ hpd h1 hpt ↦ hΛ.tendstoUniformlyOn_of_countable hpd h1 hpt, fun hunif ↦
    (Λ.relativePropertyT_iff_forall_posSemidef_norm_sub_one_lt.{u}).mpr
      (posSemidef_approx_of_tendstoUniformlyOn_nat hunif)⟩

/-- **Filter uniform-convergence characterization of relative property (T).** A subgroup `Λ` of a
countable discrete group `Γ` has relative property (T) if and only if every filter of normalized
positive-definite functions converging pointwise to `1` on `Γ` converges uniformly to `1` on `Λ`. -/
theorem relativePropertyT_iff_tendstoUniformlyOn (Λ : Subgroup Γ) :
    Λ.RelativePropertyT.{u} ↔
      ∀ (ι : Type w) (l : Filter ι) (φ : ι → Γ → ℂ),
        (∀ i, (Matrix.of fun a b : Γ ↦ φ i (a⁻¹ * b)).PosSemidef) →
          (∀ i, φ i 1 = 1) → (∀ g, Tendsto (fun i ↦ φ i g) l (𝓝 1)) →
            TendstoUniformlyOn φ 1 l Λ := by
  refine ⟨fun hΛ _ _ _ hpd h1 hpt ↦ hΛ.tendstoUniformlyOn_of_countable hpd h1 hpt, fun hunif ↦ ?_⟩
  refine (Λ.relativePropertyT_iff_tendstoUniformlyOn_nat.{u}).mpr fun φ hpd h1 hpt ↦ ?_
  have hu := hunif (ULift.{w} ℕ) (Filter.comap ULift.down atTop) (fun i ↦ φ i.down)
    (fun i ↦ hpd i.down) (fun i ↦ h1 i.down)
    (fun g ↦ (hpt g).comp Filter.tendsto_comap)
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  obtain ⟨S, hS, hS_sub⟩ := Filter.mem_comap.mp (hu ε hε)
  filter_upwards [hS] with n hn x hx
  exact hS_sub (a := ULift.up n) hn x hx

end Countable

end Subgroup
