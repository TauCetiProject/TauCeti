/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.OrbitCutoff.Discrete
public import TauCeti.MeasureTheory.Measure.Haar.Unique
import TauCeti.Algebra.Group.Subgroup.SubgroupOf
import TauCeti.MeasureTheory.Constructions.BorelSpace.Real
import TauCeti.MeasureTheory.Group.LIntegral
import TauCeti.MeasureTheory.Integral.Bochner.SMulMeasure

/-!
# Integration in Iwasawa coordinates

Let `G` be a unimodular second countable locally compact group, `N ⊂ G` a closed unimodular
subgroup, `K ⊂ G` a compact subgroup and `i : M → G` a continuous homomorphism from a unimodular
group `M`, with `G = N · i(M) · K`, and suppose that conjugation by `i(m)` multiplies the Haar
measure of `N` by `w(m) > 0`. Then the measure `dn dm dk` in the coordinates `i(m) n k` is a
multiple of the Haar measure of `G` (`MeasureTheory.exists_lintegral_iwasawa_eq_mul`); the constant
is not computed, and may be infinite.

Combined with a discrete subgroup `Γ` with `Γ ∩ N` cocompact in `N` and `Γ = (Γ ∩ N) · i(Δ)`, the
integral over `Γ \ G` of a function `F` left invariant under `N` and `Γ` is
`c ∫_{Δ\M} ∫_K w(m) F(i(m) k) dk dm` for a constant `c ≠ 0`
(`MeasureTheory.exists_integral_cutoffMeasure_iwasawa`). Here unimodularity of `N` is not assumed:
it follows from cocompactness of `Γ ∩ N`. The quotient `Δ \ M` is described by a measure `α` on `M`
whose unfolding along `Δ` is the Haar measure of `M`.

## Main results

* `MeasureTheory.exists_lintegral_iwasawa_eq_mul`: the Iwasawa integration formula, up to a
  constant.
* `MeasureTheory.exists_integral_cutoffMeasure_iwasawa`: integration over `Γ \ G` in Iwasawa
  coordinates.

The proofs use the measurable choice of rescaling factors
(`MeasureTheory.exists_measurable_mul_eq_of_scale`), the division of an integral formula by a factor
`c ∈ (0, ∞]` of the measure (`MeasureTheory.exists_integral_eq_mul_of_smul_measure`), the splitting
`D × (Γ ∩ N) ≃ Γ` of a subgroup along a complement (`Subgroup.exists_equiv_prod_subgroupOf`), and
the averaged change of variables `x = b(p) y k⁻¹` for a two-sided invariant measure
(`MeasureTheory.lintegral_mul_lintegral_translate`).

## References

* A. W. Knapp, *Lie groups beyond an introduction*, second edition, Birkhäuser, 2002, Proposition
  8.43, for the Iwasawa integration formula of a reductive group.

The statements and proofs are adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache
2.0, Copyright 2026 Anthropic PBC), `src/Lib/Adelic/QuotientMeasure/IwasawaUnfolding.lean`
(`New.ofReal_mul_lintegral_iwasawa_translate`, `New.lintegral_iwasawa_inv_mul_translate`,
`New.lintegral_iwasawa`, `New.ofReal_mul_lintegral_quotMeasure_tsum`,
`New.integral_quotMeasure_iwasawa`).
-/

public section

open MeasureTheory Measure Set Function ProbabilityTheory

open scoped ENNReal Pointwise

namespace MeasureTheory

variable {G M : Type*} [Group G] [Group M] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [TopologicalSpace M] [IsTopologicalGroup M]
  [MeasurableSpace M] [BorelSpace M] {w : M → ℝ}
  {ν : Measure M} [ν.IsMulRightInvariant] {N K : Subgroup G} [CompactSpace K]
  {κ : Measure K} [κ.IsHaarMeasure] {lam : Measure N} {i : M →* G}

omit [CompactSpace K] [κ.IsHaarMeasure] in
/-- Moving `n i(m) k` through the Iwasawa coordinates multiplies the integral by `w(m)`. -/
private theorem ofReal_mul_lintegral_iwasawa_translate [lam.IsMulRightInvariant]
    [κ.IsMulRightInvariant]
    (h_conj : ∀ m (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ n : N, f (i m * n * (i m)⁻¹) ∂lam = .ofReal (w m) * ∫⁻ n : N, f n ∂lam)
    {f : G → ℝ≥0∞} (hf : Measurable f) (n : N) (m : M) (k : K) :
    .ofReal (w m) * ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, f (i a * u * (n * i m * k) * l⁻¹) ∂lam ∂ν ∂κ =
      ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, f (i a * u * l⁻¹) ∂lam ∂ν ∂κ := by
  -- Absorb `n` into `u`, move `i(m)` past `u`, then absorb `m` into `a` and `k` into `l`.
  have h_move (x z : G) : .ofReal (w m) * ∫⁻ u : N, f (x * u * (n * i m * k) * z) ∂lam =
      ∫⁻ u : N, f (x * i m * u * (k * z)) ∂lam :=
    calc .ofReal (w m) * ∫⁻ u : N, f (x * u * (n * i m * k) * z) ∂lam
      _ = .ofReal (w m) * ∫⁻ u : N, f (x * u * i m * (k * z)) ∂lam := by
        rw [← lintegral_mul_right_eq_self (fun u : N ↦ f (x * u * i m * (k * z))) n]
        simp [mul_assoc]
      _ = ∫⁻ u : N, f (x * (i m * u * (i m)⁻¹) * i m * (k * z)) ∂lam :=
        (h_conj m (fun y ↦ f (x * y * i m * (k * z))) (by fun_prop)).symm
      _ = ∫⁻ u : N, f (x * i m * u * (k * z)) ∂lam := by simp [mul_assoc]
  calc
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, f (i (a * m) * u * (k * l⁻¹)) ∂lam ∂ν ∂κ := by
      simp only [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, map_mul, ← h_move]
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, f (i a * u * (k * l⁻¹)) ∂lam ∂ν ∂κ :=
      lintegral_congr fun l ↦
        lintegral_mul_right_eq_self (fun a : M ↦ ∫⁻ u : N, f (i a * u * (k * l⁻¹)) ∂lam) m
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, f (i a * u * l⁻¹) ∂lam ∂ν ∂κ := by
      rw [← lintegral_mul_right_eq_self _ k]
      simp

omit [ν.IsMulRightInvariant] [CompactSpace K] [κ.IsHaarMeasure] in
/-- Translating the argument by `n i(m) k` does not change the integral of `g ((i(a) u)⁻¹ x l)` in
the Iwasawa coordinates. -/
private theorem lintegral_iwasawa_inv_mul_translate [ν.IsMulLeftInvariant]
    [κ.IsMulLeftInvariant] [lam.IsMulLeftInvariant]
    (h_conj : ∀ m (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ n : N, f (i m * n * (i m)⁻¹) ∂lam = .ofReal (w m) * ∫⁻ n : N, f n ∂lam)
    {g : G → ℝ≥0∞} (hg : Measurable g) (n : N) (m : M) (k : K) :
    ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * (n * i m * k * l)) ∂lam ∂ν ∂κ =
      ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * l) ∂lam ∂ν ∂κ := by
  -- Move `(i a)⁻¹` past `u⁻¹` to absorb `n` into `u`; then absorb `m` into `a` and `k` into `l`.
  have h_absorb (a : M) (z : G) :
      ∫⁻ u : N, g ((i a * u)⁻¹ * (n * z)) ∂lam = ∫⁻ u : N, g ((i a * u)⁻¹ * z) ∂lam := by
    have h_move (y : G) : ∫⁻ u : N, g ((i a * u)⁻¹ * y) ∂lam =
        .ofReal (w a) * ∫⁻ u : N, g ((i a)⁻¹ * ((u : G)⁻¹ * y)) ∂lam := by
      simpa [mul_assoc] using h_conj a (fun x ↦ g ((i a)⁻¹ * (x⁻¹ * y))) (by fun_prop)
    rw [h_move, h_move, ← lintegral_mul_left_eq_self _ n]
    simp [mul_assoc]
  calc
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * (i m * (k * l))) ∂lam ∂ν ∂κ := by
      simp only [mul_assoc, h_absorb]
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * (k * l)) ∂lam ∂ν ∂κ := by
      refine lintegral_congr fun l ↦ ?_
      rw [← lintegral_mul_left_eq_self _ m]
      simp [mul_assoc]
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * l) ∂lam ∂ν ∂κ :=
      lintegral_mul_left_eq_self (fun l : K ↦ ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * l) ∂lam ∂ν) k

variable [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [LocallyCompactSpace M]
  [SecondCountableTopology M] [ν.IsHaarMeasure] [lam.IsHaarMeasure]

/-- **The Iwasawa integration formula**, up to a constant. Let `G` and `M` be unimodular, `N ⊂ G`
closed and unimodular, `K ⊂ G` compact, `i : M → G` a continuous homomorphism with `G = N i(M) K`,
and let conjugation by `i(m)` multiply integrals over `N` by `w(m) > 0`. Then there is
`d ∈ [0, ∞]` with `∫_K ∫_M ∫_N f(i(m) n k) dn dm dk = d ∫_G f dμ` for every measurable `f ≥ 0`. -/
theorem exists_lintegral_iwasawa_eq_mul (μ : Measure G) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] [lam.IsMulRightInvariant] (hN : IsClosed (N : Set G))
    (hw_pos : ∀ m, 0 < w m) (hi : Continuous i)
    (h_dec : ∀ g : G, ∃ (n : N) (m : M) (k : K), g = n * i m * k)
    (h_conj : ∀ m (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ n : N, f (i m * n * (i m)⁻¹) ∂lam = .ofReal (w m) * ∫⁻ n : N, f n ∂lam) :
    ∃ d : ℝ≥0∞, ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ k : K, ∫⁻ m : M, ∫⁻ n : N, f (i m * n * k) ∂lam ∂ν ∂κ = d * ∫⁻ g, f g ∂μ := by
  -- Let `J f y` be the integral of `f (i(m) n y k⁻¹)`; the left side is `J f 1`. Moving `y` only
  -- divides `J f y` by `w`, so `J f 1 = ∫ g(y) J f y dμ(y)` for a suitable weight `g`. After
  -- Fubini and a translation of `y`, this is `∫ d(x) f(x) dμ(x)`, and `d` is constant.
  have : LocallyCompactSpace N := hN.locallyCompactSpace
  have : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set G)
  have : κ.IsMulRightInvariant := isMulRightInvariant_of_isHaarMeasure_of_isFiniteMeasure κ
  have : κ.IsInvInvariant := isInvInvariant_of_isHaarMeasure_of_isFiniteMeasure κ
  obtain ⟨β, hβ⟩ := (inferInstance : HasOrbitCutoff μ G).exists_isOrbitCutoff
  have hβ_one : ∫⁻ x, β x ∂μ = 1 := by simpa using hβ.lintegral_smul 1
  let π : Measure ((M × N) × K) := (ν.prod lam).prod κ
  let b (p : M × N) : G := i p.1 * p.2
  have hπ (φ : G → K → ℝ≥0∞) (hφ : Measurable (uncurry φ)) :
      ∫⁻ h, φ (b h.1) h.2 ∂π = ∫⁻ k : K, ∫⁻ m : M, ∫⁻ n : N, φ (i m * n) k ∂lam ∂ν ∂κ := by
    rw [lintegral_prod_symm _ (by fun_prop)]
    exact lintegral_congr fun k ↦ lintegral_prod _ (by fun_prop)
  let J (f : G → ℝ≥0∞) (y : G) : ℝ≥0∞ := ∫⁻ h, f (b h.1 * y * h.2⁻¹) ∂π
  have hJ (f : G → ℝ≥0∞) (hf : Measurable f) (y : G) :
      J f y = ∫⁻ k : K, ∫⁻ m : M, ∫⁻ n : N, f (i m * n * y * k⁻¹) ∂lam ∂ν ∂κ :=
    hπ (fun x k ↦ f (x * y * k⁻¹)) (by fun_prop)
  have h_scale (y : G) : ∃ r : ℝ≥0∞, r ≠ 0 ∧ r ≠ ∞ ∧
      ∀ f : G → ℝ≥0∞, Measurable f → r * J f y = J f 1 := by
    obtain ⟨n, m, k, rfl⟩ := h_dec y
    refine ⟨.ofReal (w m), (ENNReal.ofReal_pos.2 (hw_pos m)).ne', ENNReal.ofReal_ne_top,
      fun f hf ↦ ?_⟩
    simpa only [hJ f hf, mul_one] using
      ofReal_mul_lintegral_iwasawa_translate (ν := ν) (κ := κ) h_conj hf n m k
  have hJ_meas (f : G → ℝ≥0∞) (hf : Measurable f) : Measurable (J f) :=
    Measurable.lintegral_prod_right (f := fun (y : G) (h : (M × N) × K) ↦ f (b h.1 * y * h.2⁻¹))
      (by fun_prop)
  obtain ⟨g, hg, hgJ⟩ := exists_measurable_mul_eq_of_scale hJ_meas h_scale hβ.measurable
  let d (x : G) : ℝ≥0∞ := ∫⁻ h, g ((b h.1)⁻¹ * (x * h.2)) ∂π
  have hd (x : G) : d x = d 1 := by
    obtain ⟨n, m, k, rfl⟩ := h_dec x
    have hd_eq (z : G) := hπ (fun y l ↦ g (y⁻¹ * (z * l))) (by fun_prop)
    simpa only [d, hd_eq, one_mul] using
      lintegral_iwasawa_inv_mul_translate (ν := ν) (κ := κ) h_conj hg n m k
  refine ⟨d 1, fun f hf ↦ ?_⟩
  calc ∫⁻ k : K, ∫⁻ m : M, ∫⁻ n : N, f (i m * n * k) ∂lam ∂ν ∂κ
    _ = J f 1 := by
      rw [hJ f hf, ← lintegral_inv_eq_self]
      simp
    _ = ∫⁻ y, g y * J f y ∂μ := by simp [hgJ _ f hf, lintegral_mul_const _ hβ.measurable, hβ_one]
    _ = ∫⁻ x, d x * f x ∂μ :=
      lintegral_mul_lintegral_translate μ (b := b) (by fun_prop) hg hf
    _ = d 1 * ∫⁻ x, f x ∂μ := by simp_rw [hd, lintegral_const_mul _ hf]

omit [TopologicalSpace M] [IsTopologicalGroup M] [MeasurableSpace M] [BorelSpace M]
  [LocallyCompactSpace M] [SecondCountableTopology M] [ν.IsHaarMeasure] in
/-- `w(m)` times the integral over `(Γ ∩ N) \ N` of a sum over `Γ` unfolds to a sum over `d` of
integrals over `N`. -/
private theorem ofReal_mul_lintegral_cutoffMeasure_tsum {Γ : Subgroup G} [DiscreteTopology Γ]
    (hN : IsClosed (N : Set G)) [lam.IsMulRightInvariant]
    (h_conj : ∀ m (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ n : N, f (i m * n * (i m)⁻¹) ∂lam = .ofReal (w m) * ∫⁻ n : N, f n ∂lam)
    (h_triv : ∀ a : M, i a ∈ N → a = 1) {D : Type*} [Countable D] {δ : D → M} (hδ : δ.Injective)
    (hδ_mem : ∀ d, i (δ d) ∈ Γ) (hΓ : ∀ g ∈ Γ, ∃ d, g * i (δ d) ∈ N) {f : G → ℝ≥0∞}
    (hf : Measurable f) (m : M) (k : G) :
    .ofReal (w m) *
        ∫⁻ n : N, ∑' γ : Γ, f (γ * (n * (i m * k))) ∂(Γ.subgroupOf N).cutoffMeasure lam =
      ∑' d, ∫⁻ n : N, f (i (δ d * m) * n * k) ∂lam := by
  -- Write `Γ = {i(δ d) γ}` with `γ ∈ Γ ∩ N`, unfold over `Γ ∩ N`, and move `i(m)` past `n`.
  have : LocallyCompactSpace N := hN.locallyCompactSpace
  have : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set G)
  have : lam.IsInvInvariant := isInvInvariant_of_isMulRightInvariant lam
  obtain ⟨e, he⟩ := Subgroup.exists_equiv_prod_subgroupOf h_triv hδ hδ_mem hΓ
  simp only [← e.tsum_eq, tsum_prod', he]
  have : Countable (Γ.subgroupOf N) := countable_of_Lindelof_of_discrete
  rw [lintegral_tsum fun d ↦ (Measurable.tsum fun γ ↦ by fun_prop).aemeasurable,
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun d ↦ ?_
  calc ENNReal.ofReal (w m) * ∫⁻ n : N, ∑' γ : Γ.subgroupOf N,
        f (i (δ d) * (γ : N) * (n * (i m * k))) ∂(Γ.subgroupOf N).cutoffMeasure lam
    _ = ENNReal.ofReal (w m) * ∫⁻ n : N, f (i (δ d) * n * i m * k) ∂lam := by
      rw [← lintegral_cutoffMeasure_lintegral (ν := (count : Measure (Γ.subgroupOf N)))
        (f := fun n : N ↦ f (i (δ d) * n * i m * k)) (by fun_prop)]
      simp [lintegral_count, Subgroup.smul_def, mul_assoc]
    _ = ∫⁻ n : N, f (i (δ d) * (i m * n * (i m)⁻¹) * i m * k) ∂lam :=
      (h_conj m (fun y ↦ f (i (δ d) * y * i m * k)) (by fun_prop)).symm
    _ = ∫⁻ n : N, f (i (δ d * m) * n * k) ∂lam := by simp [mul_assoc]

/-- **Unfolding in Iwasawa coordinates.** In the setting of
`MeasureTheory.exists_lintegral_iwasawa_eq_mul`, let moreover `i(a) ∈ N` only for `a = 1`, and let
`Γ ⊂ G` be discrete with `Γ ∩ N` cocompact in `N` and `Γ = (Γ ∩ N) · i(δ(D))` for an injective
`δ : D → M` from a countable set. Let `α` be a measure on `M` that unfolds to `ν` along `δ`,
standing for the quotient `δ(D) \ M`. Let `w` be measurable. There is `c ≠ 0` such that for every
measurable `F` from `G` to a real normed space, left invariant under `N` and under `Γ`, with
`(m, k) ↦ w(m) F(i(m) k)` integrable for `α × κ`, `F` is integrable over `Γ \ G` and
`∫_{Γ\G} F = c ∫∫ w(m) F(i(m) k) dα(m) dκ(k)`. -/
theorem exists_integral_cutoffMeasure_iwasawa {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure G) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] {Γ : Subgroup G} [DiscreteTopology Γ] (hN : IsClosed (N : Set G))
    (hw : Measurable w) (hw_pos : ∀ m, 0 < w m) (hi : Continuous i)
    (h_dec : ∀ g : G, ∃ (n : N) (m : M) (k : K), g = n * i m * k)
    (h_conj : ∀ m (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ n : N, f (i m * n * (i m)⁻¹) ∂lam = .ofReal (w m) * ∫⁻ n : N, f n ∂lam)
    (h_triv : ∀ a : M, i a ∈ N → a = 1) {D : Type*} [Countable D] {δ : D → M} (hδ : δ.Injective)
    (α : Measure M) [SFinite α]
    (hα : ∀ f : M → ℝ≥0∞, Measurable f → ∫⁻ m, f m ∂ν = ∫⁻ m, ∑' d, f (δ d * m) ∂α)
    (hδ_mem : ∀ d, i (δ d) ∈ Γ) (hΓ : ∀ g ∈ Γ, ∃ d, g * i (δ d) ∈ N)
    {C : Set N} (hC : IsCompact C) (hΓC : ((Γ.subgroupOf N : Set N)) * C = univ) :
    ∃ c ≠ (0 : ℝ), ∀ F : G → E, Measurable F → (∀ n ∈ N, ∀ g, F (n * g) = F g) →
      (∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) →
      Integrable (fun p : M × K ↦ w p.1 • F (i p.1 * p.2)) (α.prod κ) →
      Integrable F (Γ.cutoffMeasure μ) ∧
        ∫ g, F g ∂Γ.cutoffMeasure μ = c • ∫ p : M × K, w p.1 • F (i p.1 * p.2) ∂α.prod κ := by
  -- By the Iwasawa formula, `w (α × κ) × (Γ ∩ N) \ N` in the coordinates `n i(m) k` unfolds to
  -- `r • μ` along `Γ`; `(Γ ∩ N) \ N` has finite volume, so `N` is unimodular.
  have : LocallyCompactSpace N := hN.locallyCompactSpace
  have : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set G)
  let lam' : Measure N := (Γ.subgroupOf N).cutoffMeasure lam
  have : IsFiniteMeasure lam' := Subgroup.isFiniteMeasure_cutoffMeasure_of_isCompact _ hC hΓC
  have : lam.IsMulRightInvariant := Subgroup.isMulRightInvariant_of_isFiniteMeasure_cutoffMeasure
    (Γ.subgroupOf N)
  obtain ⟨r, h_iwa⟩ := exists_lintegral_iwasawa_eq_mul (ν := ν) (κ := κ) (lam := lam) μ hN hw_pos hi
    h_dec h_conj
  have hr : r ≠ 0 := fun h ↦ by simpa [h, NeZero.ne] using h_iwa 1 measurable_one
  have hw_meas : Measurable fun p : M × K ↦ ENNReal.ofReal (w p.1) := by fun_prop
  let ρ : Measure (M × K) := (α.prod κ).withDensity fun p ↦ .ofReal (w p.1)
  let σ (p : M × K) : G := i p.1 * p.2
  let τ (p : (M × K) × N) : G := p.2 * σ p.1
  have : Countable Γ := countable_of_Lindelof_of_discrete
  have h_unfold : MeasurePreserving (fun p : ((M × K) × N) × Γ ↦ p.2 • τ p.1)
      ((ρ.prod lam').prod count) (r • μ) := by
    refine ⟨by fun_prop, ext_of_lintegral _ fun f hf ↦ ?_⟩
    calc
      _ = ∫⁻ p : M × K, ∫⁻ n : N, ∑' γ : Γ, f (γ * (n * (i p.1 * p.2))) ∂lam' ∂ρ := by
        simp (disch := fun_prop) only [lintegral_map, lintegral_prod, lintegral_count,
          Subgroup.smul_def, smul_eq_mul, τ, σ]
      _ = ∫⁻ k : K, ∫⁻ m : M, ∑' d, ∫⁻ n : N, f (i (δ d * m) * n * k) ∂lam ∂α ∂κ := by
        rw [lintegral_withDensity_eq_lintegral_mul _ hw_meas (by fun_prop),
          lintegral_prod_symm _ (by fun_prop)]
        simp only [Pi.mul_apply, lam',
          ofReal_mul_lintegral_cutoffMeasure_tsum hN h_conj h_triv hδ hδ_mem hΓ hf]
      _ = ∫⁻ k : K, ∫⁻ m : M, ∫⁻ n : N, f (i m * n * k) ∂lam ∂ν ∂κ :=
        lintegral_congr fun k ↦ (hα (fun m ↦ ∫⁻ n : N, f (i m * n * k) ∂lam) (by fun_prop)).symm
      _ = ∫⁻ g, f g ∂(r • μ) := by rw [h_iwa f hf, lintegral_smul_measure, smul_eq_mul]
  obtain ⟨c, hc, h_div⟩ := exists_integral_eq_mul_of_smul_measure (E := E) (Γ.cutoffMeasure μ) hr
    (NeZero.ne (lam' univ)) (measure_ne_top lam' univ)
  refine ⟨c, hc, fun F hF hFN hFΓ h_weighted ↦ ?_⟩
  -- By `h_unfold`, `F` on `Γ \ G` has the law of `F ∘ τ`, which does not depend on `n`.
  have hFτ (p : (M × K) × N) : F (τ p) = F (σ p.1) := hFN p.2 p.2.property (σ p.1)
  have h_law : IdentDistrib F (fun p : M × K ↦ F (σ p)) (r • Γ.cutoffMeasure μ)
      (lam' univ • ρ) := by
    rw [Subgroup.cutoffMeasure, cutoffMeasure_def, ← withDensity_smul_measure]
    refine ((isOrbitCutoff_orbitCutoff _).identDistrib_withDensity_of_measurePreserving (T := τ)
      (.id (count : Measure Γ)) h_unfold hF (by fun_prop)
      fun γ x ↦ hFΓ γ γ.property x).trans ⟨by fun_prop, by fun_prop, ?_⟩
    simp (disch := fun_prop) only [hFτ, ← map_fst_prod, map_map, comp_def]
  have h_int : Integrable (fun p : M × K ↦ F (σ p)) ρ := by
    simpa [ρ, σ, integrable_withDensity_iff_integrable_smul' hw_meas, hw_pos, le_of_lt]
      using h_weighted
  refine h_div F _ (h_law.integrable_iff.2 (h_int.smul_measure (measure_ne_top lam' univ))) ?_
  rw [h_law.integral_eq, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hw_meas (by simp)]
  simp [σ, hw_pos, le_of_lt]

end MeasureTheory
