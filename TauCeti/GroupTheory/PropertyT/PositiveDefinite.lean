/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import TauCeti.GroupTheory.PropertyT.KazhdanPair
import TauCeti.Analysis.Matrix.PosSemidef.Exponential
import TauCeti.GroupTheory.PositiveDefinite.Basic
import TauCeti.GroupTheory.PositiveDefinite.Metric
import TauCeti.RepresentationTheory.Continuous.Unitary.OrbitConvex
import TauCeti.RepresentationTheory.Continuous.Unitary.PositiveDefinite

/-!
# Quantitative and positive-definite characterizations of relative property (T)

This file establishes the quantitative invariant-vector and positive-definite characterizations of
relative property (T) for a subgroup `Λ` of a discrete group `Γ`:

* For a normal subgroup `Λ` of an arbitrary discrete group `Γ`, quantitative Kazhdan approximation
  (`IsKazhdanPair.exists_invariant_norm_sub_lt`) yields the quantitative and net uniform-convergence
  positive-definite characterizations without countability.
* For an arbitrary subgroup `Λ` of a countable discrete group `Γ`, relative property (T) is
  equivalent to:
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

* `Subgroup.relativePropertyT_iff_forall_exists_invariant_norm_sub_lt`: quantitative
  `Λ`-invariant vector characterization for countable groups.
* `Subgroup.relativePropertyT_iff_forall_posSemidef_norm_sub_one_lt`: quantitative
  positive-definite characterization for countable groups (and `_of_normal` without countability).
* `Subgroup.RelativePropertyT.tendstoUniformlyOn`,
  `Subgroup.relativePropertyT_iff_tendstoUniformlyOn_nat`,
  `Subgroup.relativePropertyT_iff_tendstoUniformlyOn`: uniform convergence of normalized
  positive-definite functions on `Λ`.

## References

* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Proposition 14.1.2.
* P. Jolissaint, *On Property (T) for pairs of topological groups*, Enseign. Math. (2) 51 (2005),
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
  have hξ_inner : ⟪ξ, ξ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hξ]
    norm_num
  have hφ1 : φ 1 = 1 := by
    dsimp only [φ]
    rw [map_one, one_apply_eq_self, hξ_inner]
  have hφF (g : Γ) (hg : g ∈ F) : ‖φ g - 1‖ < δ := by
    have hsub : φ g - 1 = ⟪ξ, ρ g ξ - ξ⟫_ℂ := by
      dsimp only [φ]
      rw [inner_sub_right, hξ_inner]
    calc ‖φ g - 1‖ = ‖⟪ξ, ρ g ξ - ξ⟫_ℂ‖ := by rw [hsub]
      _ ≤ ‖ξ‖ * ‖ρ g ξ - ξ‖ := norm_inner_le_norm _ _
      _ = ‖ρ g ξ - ξ‖ := by rw [hξ, one_mul]
      _ < δ := hξF g hg
  have horb (k : Λ) : ‖(ρ.restrict Λ.subtype) k ξ - ξ‖ ≤ (3 / 4 : ℝ) * ε := by
    have hk := hFδ φ hφ hφ1 hφF k k.property
    have hre : 1 - (φ k).re < ε ^ 2 / 4 :=
      lt_of_le_of_lt (by simpa [norm_sub_rev] using Complex.re_le_norm (1 - φ k)) hk
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

/-- Quantitative `Λ`-invariant vector approximation in universe `v` yields quantitative
positive-definite approximation on `Λ`, via the GNS representation. -/
private theorem posSemidef_approx_of_approx_invariant {Λ : Subgroup Γ}
    (hinv : ∀ ε : ℝ, 0 < ε →
      ∃ (F : Finset Γ) (δ : ℝ), 0 < δ ∧
        ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
          (ρ : ContRepresentation ℂ Γ H), ρ.IsUnitary →
            ∀ ξ : H, ‖ξ‖ = 1 → (∀ g ∈ F, ‖ρ g ξ - ξ‖ < δ) →
              ∃ v ∈ (ρ.restrict Λ.subtype).invariants, ‖v - ξ‖ < ε) :
    PosSemidefApprox Λ := by
  intro ε hε
  obtain ⟨F, δ₀, hδ₀, hF⟩ := hinv (ε / 2) (half_pos hε)
  refine ⟨F, δ₀ ^ 2 / 2, by positivity, fun φ hφ h1 hφF h hh ↦ ?_⟩
  let ξ := hφ.gnsVector 1
  have hξ : ‖ξ‖ = 1 := hφ.norm_gnsVector_eq_one h1 1
  have hξF (g : Γ) (hg : g ∈ F) : ‖hφ.gnsRepresentation g ξ - ξ‖ < δ₀ :=
    hφ.norm_gnsRepresentation_gnsVector_one_sub_lt h1 hδ₀ (hφF g hg)
  obtain ⟨v, hv, hvξ⟩ := hF hφ.gnsSpace hφ.gnsRepresentation hφ.isUnitary_gnsRepresentation
    ξ hξ hξF
  have hvh : hφ.gnsRepresentation h v = v := hv ⟨h, hh⟩
  have hsub : φ h - 1 = ⟪ξ, hφ.gnsRepresentation h ξ - ξ⟫_ℂ := by
    rw [inner_sub_right, hφ.inner_gnsVector_one_gnsRepresentation, inner_self_eq_norm_sq_to_K, hξ]
    norm_num
  have hdiff : hφ.gnsRepresentation h ξ - ξ =
      hφ.gnsRepresentation h (ξ - v) - (ξ - v) := by
    rw [map_sub, hvh]
    abel
  calc ‖φ h - 1‖ = ‖⟪ξ, hφ.gnsRepresentation h ξ - ξ⟫_ℂ‖ := by rw [hsub]
    _ ≤ ‖ξ‖ * ‖hφ.gnsRepresentation h ξ - ξ‖ := norm_inner_le_norm _ _
    _ = ‖hφ.gnsRepresentation h (ξ - v) - (ξ - v)‖ := by rw [hξ, one_mul, hdiff]
    _ ≤ ‖hφ.gnsRepresentation h (ξ - v)‖ + ‖ξ - v‖ := norm_sub_le _ _
    _ = 2 * ‖v - ξ‖ := by
        rw [hφ.isUnitary_gnsRepresentation.norm_map, norm_sub_rev]
        ring
    _ < ε := by linarith

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

/-- Uniform convergence on `Λ` along arbitrary filters in universe `v` implies quantitative
positive-definite approximation on `Λ`. -/
private theorem posSemidef_approx_of_tendstoUniformlyOn {Λ : Subgroup Γ}
    (hunif : ∀ (ι : Type v) (l : Filter ι) (φ : ι → Γ → ℂ),
      (∀ i, (Matrix.of fun a b : Γ ↦ φ i (a⁻¹ * b)).PosSemidef) →
        (∀ i, φ i 1 = 1) → (∀ g, Tendsto (fun i ↦ φ i g) l (𝓝 1)) →
          TendstoUniformlyOn φ 1 l Λ) :
    PosSemidefApprox Λ := by
  classical
  refine posSemidef_approx_of_tendstoUniformlyOn_of_exhaustion (l := atTop)
    (fun i : Finset Γ × ℕ ↦ i.1) (fun i ↦ 1 / (i.2 + 1 : ℝ))
    (fun _ ↦ Nat.one_div_pos_of_nat)
    (fun g ↦ Filter.eventually_atTop.mpr ⟨({g}, 0), fun i hi ↦ hi.1 (Finset.mem_singleton_self g)⟩)
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp
      (Filter.tendsto_atTop_atTop.mpr fun n ↦ ⟨(∅, n), fun _ hi ↦ hi.2⟩))
    (hunif (Finset Γ × ℕ) atTop)

/-- When `Γ` is countable, sequential uniform convergence on `Λ` already implies quantitative
positive-definite approximation on `Λ`. -/
private theorem posSemidef_approx_of_tendstoUniformlyOn_nat [Countable Γ] {Λ : Subgroup Γ}
    (hunif : ∀ φ : ℕ → Γ → ℂ,
      (∀ n, (Matrix.of fun a b : Γ ↦ φ n (a⁻¹ * b)).PosSemidef) →
        (∀ n, φ n 1 = 1) → (∀ g, Tendsto (fun n ↦ φ n g) atTop (𝓝 1)) →
          TendstoUniformlyOn φ 1 atTop Λ) :
    PosSemidefApprox Λ := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat Γ
  refine posSemidef_approx_of_tendstoUniformlyOn_of_exhaustion (l := atTop)
    (fun n : ℕ ↦ (Finset.range (n + 1)).image e) (fun n ↦ 1 / (n + 1 : ℝ))
    (fun _ ↦ Nat.one_div_pos_of_nat) (fun g ↦ ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat hunif
  obtain ⟨k₀, rfl⟩ := he g
  exact Filter.eventually_atTop.mpr ⟨k₀, fun n hn ↦
    Finset.mem_image_of_mem e (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))⟩

omit [Group Γ] in
/-- Summability of the weighted series `∑' k, (k + 1) * (1 - φ k g)` along an exhaustion of `Γ`. -/
private theorem summable_mul_one_sub_of_exhaustion [DecidableEq Γ] {e : ℕ → Γ}
    (he : Function.Surjective e) {A : ℕ → Finset Γ}
    (hA : ∀ k, (Finset.range (k + 1)).image e ⊆ A k) {φ : ℕ → Γ → ℂ}
    (hF : ∀ k, ∀ g ∈ A k, ‖φ k g - 1‖ ≤ 1 / ((k + 1 : ℝ) * (2 : ℝ) ^ (k + 1))) (g : Γ) :
    Summable fun k : ℕ ↦ ((k + 1 : ℝ) : ℂ) * (1 - φ k g) := by
  obtain ⟨k₀, rfl⟩ := he g
  have hgeom : Summable fun k : ℕ ↦ ((1 / 2 : ℝ) ^ (k + 1)) :=
    (summable_geometric_two.mul_left (1 / 2)).congr fun k ↦ by ring
  refine Summable.of_norm_bounded_eventually_nat hgeom ?_
  refine Filter.eventually_atTop.mpr ⟨k₀, fun k hk ↦ ?_⟩
  have hmem : e k₀ ∈ A k :=
    hA k (Finset.mem_image_of_mem e (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
  have hlt := hF k (e k₀) hmem
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_sub_rev]
  calc (k + 1 : ℝ) * ‖φ k (e k₀) - 1‖
      ≤ (k + 1 : ℝ) * (1 / ((k + 1 : ℝ) * (2 : ℝ) ^ (k + 1))) := by gcongr
    _ = (1 / 2 : ℝ) ^ (k + 1) := by
        rw [one_div, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul, ← inv_pow,
          ← one_div]

/-- Exponential decay of double translates `Φ (a⁻¹ * s n * b)` along the bad sequence `s`. -/
private theorem tendsto_cexp_neg_tsum_mul_zero [DecidableEq Γ] {e : ℕ → Γ}
    (he : Function.Surjective e) {A : ℕ → Finset Γ}
    (hA : ∀ k, (Finset.range (k + 1)).image e ⊆ A k)
    {φ : ℕ → Γ → ℂ} (hpd : ∀ k, (Matrix.of fun a b : Γ ↦ φ k (a⁻¹ * b)).PosSemidef)
    (h1 : ∀ k, φ k 1 = 1)
    (hsumm : ∀ g, Summable fun k : ℕ ↦ ((k + 1 : ℝ) : ℂ) * (1 - φ k g))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hF : ∀ k, ∀ g ∈ A k, ‖φ k g - 1‖ < ε₀ ^ 2 / 32)
    {s : ℕ → Γ} (hsε : ∀ k, ε₀ ≤ ‖φ k (s k) - 1‖) {t : ℝ} (ht : 0 < t) (a b : Γ) :
    Tendsto (fun n ↦ Complex.exp (-(t : ℂ) *
      ∑' k : ℕ, ((k + 1 : ℝ) : ℂ) * (1 - φ k (a⁻¹ * s n * b)))) atTop (𝓝 0) := by
  obtain ⟨ka, rfl⟩ := he a
  obtain ⟨kb, rfl⟩ := he b
  let ψ (g : Γ) : ℂ := ∑' k : ℕ, ((k + 1 : ℝ) : ℂ) * (1 - φ k g)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖Complex.exp (-(t : ℂ) * ψ ((e ka)⁻¹ * s n * e kb))‖ ≤
        Real.exp (-(t * (ε₀ ^ 2 / 8)) * (n + 1 : ℝ)) := by
    refine Filter.eventually_atTop.mpr ⟨max ka kb, fun n hn ↦ ?_⟩
    have ha_mem : e ka ∈ A n := hA n <|
      Finset.mem_image_of_mem e (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_of_max_le_left hn)))
    have hb_mem : e kb ∈ A n := hA n <|
      Finset.mem_image_of_mem e (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_of_max_le_right hn)))
    have hre_ge : ε₀ ^ 2 / 8 ≤ 1 - (φ n ((e ka)⁻¹ * s n * e kb)).re := by
      let u : ℝ := Real.sqrt (ε₀ ^ 2 / 32)
      have hu2 : u ^ 2 = ε₀ ^ 2 / 32 := Real.sq_sqrt (by positivity)
      have htri₁ := (hpd n).sqrt_re_one_sub_re_mul_le (e ka * ((e ka)⁻¹ * s n * e kb)) (e kb)⁻¹
      have htri₂ := (hpd n).sqrt_re_one_sub_re_mul_le (e ka) ((e ka)⁻¹ * s n * e kb)
      have hinv : (φ n (e kb)⁻¹).re = (φ n (e kb)).re := by
        rw [(hpd n).isHermitian.apply_inv_eq_star (e kb), Complex.star_def, Complex.conj_re]
      have hprod : e ka * ((e ka)⁻¹ * s n * e kb) * (e kb)⁻¹ = s n := by group
      simp only [RCLike.re_to_complex, hprod, h1 n, Complex.one_re, hinv] at htri₁
      simp only [RCLike.re_to_complex, h1 n, Complex.one_re] at htri₂
      have hre_a : 1 - (φ n (e ka)).re ≤ ε₀ ^ 2 / 32 :=
        le_trans (by simpa [norm_sub_rev] using Complex.re_le_norm (1 - φ n (e ka)))
          (hF n _ ha_mem).le
      have hre_b : 1 - (φ n (e kb)).re ≤ ε₀ ^ 2 / 32 :=
        le_trans (by simpa [norm_sub_rev] using Complex.re_le_norm (1 - φ n (e kb)))
          (hF n _ hb_mem).le
      have hsq_s : (4 * u) ^ 2 ≤ 1 - (φ n (s n)).re := by
        have hnorm : ‖φ n (s n) - 1‖ ^ 2 ≤ 2 * (1 - (φ n (s n)).re) :=
          (hpd n).norm_sub_one_sq_le (h1 n) (s n)
        have hε_sq : ε₀ ^ 2 ≤ ‖φ n (s n) - 1‖ ^ 2 := pow_le_pow_left₀ hε₀.le (hsε n) 2
        nlinarith
      have hsqrt_s : 4 * u ≤ Real.sqrt (1 - (φ n (s n)).re) :=
        Real.le_sqrt_of_sq_le hsq_s
      have hsqrt_a : Real.sqrt (1 - (φ n (e ka)).re) ≤ u := Real.sqrt_le_sqrt hre_a
      have hsqrt_b : Real.sqrt (1 - (φ n (e kb)).re) ≤ u := Real.sqrt_le_sqrt hre_b
      have hsqrt_mid : 2 * u ≤ Real.sqrt (1 - (φ n ((e ka)⁻¹ * s n * e kb)).re) := by
        linarith
      have hsq_mid : (2 * u) ^ 2 ≤ (Real.sqrt (1 - (φ n ((e ka)⁻¹ * s n * e kb)).re)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hsqrt_mid 2
      rw [Real.sq_sqrt (by simpa using (hpd n).one_sub_re_nonneg (h1 n) _)] at hsq_mid
      nlinarith
    have hsumm_re : Summable fun k : ℕ ↦ (k + 1 : ℝ) * (1 - (φ k ((e ka)⁻¹ * s n * e kb)).re) := by
      simpa using Complex.reCLM.summable (hsumm ((e ka)⁻¹ * s n * e kb))
    have hψ_re : (ψ ((e ka)⁻¹ * s n * e kb)).re =
        ∑' k : ℕ, (k + 1 : ℝ) * (1 - (φ k ((e ka)⁻¹ * s n * e kb)).re) := by
      simpa [ψ] using Complex.reCLM.map_tsum (hsumm ((e ka)⁻¹ * s n * e kb))
    have htsum_ge : (n + 1 : ℝ) * (ε₀ ^ 2 / 8) ≤ (ψ ((e ka)⁻¹ * s n * e kb)).re := by
      rw [hψ_re]
      exact (mul_le_mul_of_nonneg_left hre_ge (by positivity)).trans <|
        hsumm_re.le_tsum n fun k _ ↦ mul_nonneg (by positivity)
          ((hpd k).one_sub_re_nonneg (h1 k) _)
    rw [Complex.norm_exp, show (-(t : ℂ) * ψ ((e ka)⁻¹ * s n * e kb)).re =
        -t * (ψ ((e ka)⁻¹ * s n * e kb)).re by simp]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hexp0 : Tendsto (fun n : ℕ ↦ Real.exp (-(t * (ε₀ ^ 2 / 8)) * (n + 1 : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp <|
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop_of_neg
        (by nlinarith [sq_pos_of_pos hε₀])
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) hbound hexp0

/-- **Jolissaint – Anantharaman–Popa exponential step.** For a subgroup `Λ` of a countable group
`Γ`, relative property (T) implies quantitative positive-definite approximation on `Λ`. -/
private theorem posSemidef_approx_of_relativePropertyT [Countable Γ] {Λ : Subgroup Γ}
    (hΛ : Λ.RelativePropertyT.{v}) : PosSemidefApprox Λ := by
  classical
  obtain ⟨F₀, δ₀, hδ₀, hK⟩ := Λ.relativePropertyT_iff_exists_isKazhdanPair.{v, v}.mp hΛ
  by_contra hnot
  unfold PosSemidefApprox at hnot
  push Not at hnot
  obtain ⟨ε₀, hε₀, hbad⟩ := hnot
  obtain ⟨e, he⟩ := exists_surjective_nat Γ
  let A (k : ℕ) : Finset Γ := F₀ ∪ (Finset.range (k + 1)).image e
  let η (k : ℕ) : ℝ := min (1 / ((k + 1 : ℝ) * (2 : ℝ) ^ (k + 1))) (ε₀ ^ 2 / 32)
  have hex (k : ℕ) := hbad (A k) (η k) (by positivity)
  choose φ hpd h1 hF s hsΛ hsε using hex
  have hA_sub (k : ℕ) : (Finset.range (k + 1)).image e ⊆ A k := Finset.subset_union_right
  have hsumm (g : Γ) : Summable fun k : ℕ ↦ ((k + 1 : ℝ) : ℂ) * (1 - φ k g) :=
    summable_mul_one_sub_of_exhaustion he hA_sub
      (fun k x hx ↦ (hF k x hx).le.trans (min_le_left _ _)) g
  let ψ (g : Γ) : ℂ := ∑' k : ℕ, ((k + 1 : ℝ) : ℂ) * (1 - φ k g)
  -- Pick `t > 0` small enough that `exp (-t * ψ g)` is within `δ₀ ^ 2 / 2` of `1` on `F₀`.
  have hev_t : ∀ᶠ t : ℝ in 𝓝 0,
      ∀ g ∈ F₀, ‖Complex.exp (-(t : ℂ) * ψ g) - 1‖ < δ₀ ^ 2 / 2 := by
    refine (Filter.eventually_all_finset F₀).mpr fun g _ ↦ ?_
    have hcont : Continuous fun t : ℝ ↦ Complex.exp (-(t : ℂ) * ψ g) := by fun_prop
    have ht0 : Tendsto (fun t : ℝ ↦ Complex.exp (-(t : ℂ) * ψ g)) (𝓝 0) (𝓝 1) := by
      simpa using (hcont.continuousAt (x := 0)).tendsto
    simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp ht0 (δ₀ ^ 2 / 2) (by positivity)
  obtain ⟨r, hr, hr_sub⟩ := Metric.mem_nhds_iff.mp hev_t
  let t : ℝ := r / 2
  have ht : 0 < t := half_pos hr
  have htF₀ : ∀ g ∈ F₀, ‖Complex.exp (-(t : ℂ) * ψ g) - 1‖ < δ₀ ^ 2 / 2 :=
    hr_sub (by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_of_nonneg ht.le]
      exact half_lt_self hr)
  let Φ (g : Γ) : ℂ := Complex.exp (-(t : ℂ) * ψ g)
  have hΦ : (Matrix.of fun a b : Γ ↦ Φ (a⁻¹ * b)).PosSemidef := by
    let K (k : ℕ) : Matrix Γ Γ ℂ :=
      ((t * (k + 1 : ℝ) : ℝ) : ℂ) • Matrix.of fun a b : Γ ↦ φ k (a⁻¹ * b)
    have hK (k : ℕ) : (K k).PosSemidef :=
      (hpd k).smul (by exact_mod_cast mul_nonneg ht.le (by positivity : (0 : ℝ) ≤ k + 1))
    let c (k : ℕ) : ℝ := t * (k + 1 : ℝ)
    have hterm (a b : Γ) (k : ℕ) :
        -(t : ℂ) * (((k + 1 : ℝ) : ℂ) * (1 - φ k (a⁻¹ * b))) = K k a b - (c k : ℂ) := by
      simp only [K, c, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Complex.ofReal_mul]
      ring
    have hsumm' (a b : Γ) : Summable fun k : ℕ ↦ K k a b - (c k : ℂ) :=
      ((hsumm (a⁻¹ * b)).mul_left (-(t : ℂ))).congr (hterm a b)
    have htsum_eq (a b : Γ) :
        -(t : ℂ) * ψ (a⁻¹ * b) = ∑' k : ℕ, (K k a b - (c k : ℂ)) := by
      rw [show -(t : ℂ) * ψ (a⁻¹ * b) =
          ∑' k : ℕ, -(t : ℂ) * (((k + 1 : ℝ) : ℂ) * (1 - φ k (a⁻¹ * b))) from
        tsum_mul_left.symm]
      exact tsum_congr (hterm a b)
    simpa only [Φ, htsum_eq] using TauCeti.posSemidef_cexp_tsum_sub hK hsumm'
  have hΦ1 : Φ 1 = 1 := by simp [Φ, ψ, h1]
  obtain ⟨v, hv0, hvΛ⟩ := (isKazhdanPair_def Λ F₀ δ₀).mp hK
    hΦ.gnsSpace hΦ.gnsRepresentation hΦ.isUnitary_gnsRepresentation
    ⟨hΦ.gnsVector 1, hΦ.norm_gnsVector_eq_one hΦ1 1,
      fun g hg ↦ hΦ.norm_gnsRepresentation_gnsVector_one_sub_lt hΦ1 hδ₀ (htF₀ g hg)⟩
  have hbot : (hΦ.gnsRepresentation.restrict Λ.subtype).invariants = ⊥ :=
    hΦ.invariants_restrict_gnsRepresentation_eq_bot Λ.subtype (s := fun n ↦ ⟨s n, hsΛ n⟩)
      (tendsto_cexp_neg_tsum_mul_zero he hA_sub hpd h1 hsumm hε₀
        (fun k x hx ↦ (hF k x hx).trans_le (min_le_right _ _)) hsε ht)
  exact hv0 ((Submodule.mem_bot ℂ).mp (hbot ▸ hvΛ))

end Bridges

/-! ### Main characterizations of relative property (T) -/

/-- **Positive-definite characterization for normal subgroups.** Without any countability assumption
on `Γ`, a normal subgroup `Λ` has relative property (T) in the universe `v` of `Γ` if and only if
normalized positive-definite functions close to `1` on a finite set are uniformly close to `1` on
`Λ`. -/
theorem relativePropertyT_iff_forall_posSemidef_norm_sub_one_lt_of_normal
    (Λ : Subgroup Γ) [Λ.Normal] :
    Λ.RelativePropertyT.{v} ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ (F : Finset Γ) (δ : ℝ), 0 < δ ∧
          ∀ φ : Γ → ℂ, (Matrix.of fun a b : Γ ↦ φ (a⁻¹ * b)).PosSemidef → φ 1 = 1 →
            (∀ g ∈ F, ‖φ g - 1‖ < δ) → ∀ h ∈ Λ, ‖φ h - 1‖ < ε := by
  refine ⟨fun hΛ ↦ ?_, fun hpd_approx ↦ ?_⟩
  · obtain ⟨F, δ, hδ, hK⟩ := Λ.relativePropertyT_iff_exists_isKazhdanPair.{v, v}.mp hΛ
    exact posSemidef_approx_of_approx_invariant fun ε hε ↦
      ⟨F, ε * δ, mul_pos hε hδ, fun H _ _ _ ρ hρ ξ _ hξF ↦
        hK.exists_invariant_norm_sub_lt hδ hρ hε ξ hξF⟩
  · obtain ⟨F, δ, hδ, hF⟩ := approx_invariant_of_posSemidef_approx.{v} hpd_approx zero_lt_one
    exact (isKazhdanPair_of_exists_invariant_norm_sub_lt_one hF).relativePropertyT hδ

/-- For a normal subgroup `Λ` with relative property (T) in the universe `v` of `Γ`, every filter
of normalized positive-definite functions converging pointwise to `1` on `Γ` converges uniformly
to `1` on `Λ`. -/
theorem RelativePropertyT.tendstoUniformlyOn_of_normal {Λ : Subgroup Γ} [Λ.Normal]
    (hΛ : Λ.RelativePropertyT.{v}) {ι : Type w} {l : Filter ι} {φ : ι → Γ → ℂ}
    (hpd : ∀ i, (Matrix.of fun a b : Γ ↦ φ i (a⁻¹ * b)).PosSemidef)
    (h1 : ∀ i, φ i 1 = 1) (hpt : ∀ g, Tendsto (fun i ↦ φ i g) l (𝓝 1)) :
    TendstoUniformlyOn φ 1 l Λ :=
  tendstoUniformlyOn_of_posSemidef_approx
    ((relativePropertyT_iff_forall_posSemidef_norm_sub_one_lt_of_normal Λ).mp hΛ) hpd h1 hpt

/-- **Net uniform-convergence characterization for normal subgroups.** Without countability, a
normal subgroup `Λ` has relative property (T) in the universe `v` of `Γ` if and only if every
filter of normalized positive-definite functions converging pointwise to `1` on `Γ` converges
uniformly to `1` on `Λ`. -/
theorem relativePropertyT_iff_tendstoUniformlyOn_of_normal (Λ : Subgroup Γ) [Λ.Normal] :
    Λ.RelativePropertyT.{v} ↔
      ∀ (ι : Type v) (l : Filter ι) (φ : ι → Γ → ℂ),
        (∀ i, (Matrix.of fun a b : Γ ↦ φ i (a⁻¹ * b)).PosSemidef) →
          (∀ i, φ i 1 = 1) → (∀ g, Tendsto (fun i ↦ φ i g) l (𝓝 1)) →
            TendstoUniformlyOn φ 1 l Λ :=
  ⟨fun hΛ _ _ _ hpd h1 hpt ↦ hΛ.tendstoUniformlyOn_of_normal hpd h1 hpt, fun hunif ↦
    (relativePropertyT_iff_forall_posSemidef_norm_sub_one_lt_of_normal Λ).mpr
      (posSemidef_approx_of_tendstoUniformlyOn hunif)⟩

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
            (∀ g ∈ F, ‖φ g - 1‖ < δ) → ∀ h ∈ Λ, ‖φ h - 1‖ < ε := by
  refine ⟨fun hΛ ↦ posSemidef_approx_of_relativePropertyT hΛ.of_universe, fun hpd_approx ↦ ?_⟩
  exact (Λ.relativePropertyT_iff_forall_exists_invariant_norm_sub_lt.{u}).mpr fun ε hε ↦
    approx_invariant_of_posSemidef_approx hpd_approx hε

/-- **Uniform convergence of positive-definite nets.** If a subgroup `Λ` of a countable discrete
group `Γ` has relative property (T), every filter of normalized positive-definite functions
converging pointwise to `1` on `Γ` converges uniformly to `1` on `Λ`. -/
theorem RelativePropertyT.tendstoUniformlyOn {Λ : Subgroup Γ} (hΛ : Λ.RelativePropertyT.{u})
    {ι : Type w} {l : Filter ι} {φ : ι → Γ → ℂ}
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
  ⟨fun hΛ _ hpd h1 hpt ↦ hΛ.tendstoUniformlyOn hpd h1 hpt, fun hunif ↦
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
  refine ⟨fun hΛ _ _ _ hpd h1 hpt ↦ hΛ.tendstoUniformlyOn hpd h1 hpt, fun hunif ↦ ?_⟩
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
