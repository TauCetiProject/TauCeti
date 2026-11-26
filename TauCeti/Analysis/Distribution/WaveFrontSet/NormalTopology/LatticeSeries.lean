/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.NormalTopology
public import TauCeti.Analysis.Distribution.TestFunction.FourierSeries
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.Convex.Cone.InfDist
import TauCeti.Analysis.Distribution.TestFunction.DominatedSeries
import TauCeti.Analysis.Distribution.TestFunction.LatticeSeries
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.TestFunction.Schwartz
import TauCeti.Analysis.Fourier.Continuous
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.Normed.Module.Cone

/-!
# Lattice series of localized Fourier transforms in the normal topology

Let `T` be a distribution on an open set `W` of a finite-dimensional real inner product space
`F`, with wave front set in a cone `Γ`, let `χ` be a cutoff on `W`, `L` a full lattice of `F`,
and `B : F →L[ℝ] E` a linear map to a second such space. Pulling a distribution back along a
linear map with transpose `B` turns its localized Fourier transforms into lattice series

`∑ m : L^∨, (covolume L)⁻¹ 𝓕 φ (ξ + B m) T (χ e_(-m))`,

for a cutoff `φ` on an open set `U` of `E` and a frequency `ξ ∈ E`. This happens for the
restriction to `E × {0}`, where `B` is the projection `(ξ, η) ↦ ξ`
(`Distribution.localFourier_pullbackInl_eq_tsum`), and for the pullback along a surjective linear
map, where `B` is its transpose (`Distribution.localFourier_compCLMOfSubmersion_linear_eq_tsum`).
This
file proves the estimates on these series which make both pullbacks continuous for the normal
topologies of Hörmander's spaces `𝓓'_Γ`.

Let `V` be a closed cone of `E` and `ε > 0` such that no point of `Γ` lies over the support of
`χ` in a direction of the closed cone

`A = {η | dist (B η, V) ≤ ε ‖η‖}`.

Then, for `ξ ∈ V`, the series, weighted by `(1 + ‖ξ‖) ^ N`, is bounded by a continuous seminorm of
`𝓓'_Γ(W)` (`TauCeti.WaveFrontSpace.exists_continuous_seminorm_one_add_norm_pow_mul_norm_tsum_le`),
and so are the series at `ξ = 0` for cutoffs `φ` in a compact set when `V = {0}`
(`TauCeti.WaveFrontSpace.exists_continuous_seminorm_norm_tsum_le`).

## The estimates

The terms with `-m ∈ A` are controlled by the seminorms `‖T‖_{χ,A,M}`. Off `A`, `‖ξ + B m‖` is
comparable to `‖ξ‖ + ‖m‖` for `ξ ∈ V`, so the coefficients `𝓕 φ (ξ + B m)` decay rapidly in `ξ`
and `m` jointly, and these terms sum to the pairing of `T` with a single test function: the Fourier
series `∑ m, (covolume L)⁻¹ 𝓕 φ (ξ + B m) χ e_(-m)` restricted to these `m`, which converges in
the smooth functions supported in `tsupport χ`. Weighted by `(1 + ‖ξ‖) ^ N`, these test functions
depend continuously on `ξ ∈ V` and tend to zero at infinity, so together with `0` they form a
compact set (`ContDiffMapSupportedIn.isCompact_insert_range_tsum_one_add_pow_mul_smul_modulate`),
on which `T` is bounded by a continuous seminorm of `𝓓'(W)`
(`TauCeti.WaveFrontSpace.exists_continuous_seminorm_norm_complexPairing_le`). At `ξ = 0`, the same
test functions depend continuously on `φ`.

## Main results

* `TauCeti.WaveFrontSpace.exists_continuous_seminorm_one_add_norm_pow_mul_norm_tsum_le`: the
  weighted lattice series for a fixed cutoff `φ` and `ξ ∈ V`.
* `TauCeti.WaveFrontSpace.exists_continuous_seminorm_norm_tsum_le`: the lattice series at
  `ξ = 0` for cutoffs `φ` in a compact set.
* `TauCeti.WaveFrontSpace.exists_forall_mem_thickening_forall_notMem`: if `B η ∉ V` for the
  covectors `(y, η) ∈ Γ` over a compact set `K`, no point of `Γ` lies over a neighbourhood of `K` in
  a direction of the cone `A`.
* `TauCeti.WaveFrontSpace.exists_cutoff_eqOn_one_forall_notMem`: a cutoff `χ` equal to one on `K`
  with no point of `Γ` over its support in a direction of `A`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.4 (the pullback and its sequential continuity on `𝓓'_Γ`).
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set (with a counterexample by Semyon Alesker)*, Studia Math. 232
  (2016), arXiv:1409.7662v2, Theorem 6.3 (continuity of the pullback in the normal topology).
-/

public section

noncomputable section

open Complex Filter Function Metric Set TopologicalSpace TestFunction
open scoped Distributions Topology FourierTransform ContDiff Real RealInnerProductSpace Pointwise
  SchwartzMap

namespace TauCeti

open Distribution

namespace WaveFrontSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {U : Opens E} {W : Opens F} {Γ : Set (F × F)}

/-! ### The cone `A` of the source seminorms -/

/-- The closed cone `A = {η | dist (B η, V) ≤ ε ‖η‖}` of the covectors whose image under `B` is
within `ε ‖η‖` of `V`. -/
private def bigCone (B : F →L[ℝ] E) (V : Set E) (ε : ℝ) : Set F :=
  {η | infDist (B η) V ≤ ε * ‖η‖}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem isClosed_bigCone (B : F →L[ℝ] E) (V : Set E) (ε : ℝ) :
    IsClosed (bigCone B V ε) :=
  isClosed_le ((continuous_infDist_pt V).comp B.continuous) (continuous_const.mul continuous_norm)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem smul_mem_bigCone (B : F →L[ℝ] E) {V : Set E}
    (hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ V, t • ξ ∈ V) {ε : ℝ} (t : ℝ) (ht : 0 < t)
    (η : F) (hη : η ∈ bigCone B V ε) : t • η ∈ bigCone B V ε := by
  simp only [bigCone, mem_ofPred_eq, norm_smul, Real.norm_of_nonneg ht.le] at hη ⊢
  rw [map_smul, infDist_smul_of_smul_mem hVcone ht]
  calc t * infDist (B η) V ≤ t * (ε * ‖η‖) := by gcongr
    _ = ε * (t * ‖η‖) := by ring

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Off the cone `A`, the image under `B` of a covector stays away from `V`:
`ε / (1 + ‖B‖ + ε) (‖ξ‖ + ‖η‖) ≤ ‖B η - ξ‖` for `ξ ∈ V`. -/
private theorem mul_add_le_norm_sub (B : F →L[ℝ] E) {V : Set E} {ε : ℝ} (hε : 0 < ε) {ξ : E}
    (hξ : ξ ∈ V) {η : F} (hη : η ∉ bigCone B V ε) :
    ε / (1 + ‖B‖ + ε) * (‖ξ‖ + ‖η‖) ≤ ‖B η - ξ‖ := by
  simp only [bigCone, mem_ofPred_eq, not_le] at hη
  have h1 : ε * ‖η‖ ≤ ‖B η - ξ‖ :=
    hη.le.trans ((infDist_le_dist_of_mem hξ).trans_eq (dist_eq_norm _ _))
  have h2 : ‖ξ‖ - ‖B‖ * ‖η‖ ≤ ‖B η - ξ‖ := by
    have h3 := norm_sub_norm_le ξ (B η)
    have h4 := B.le_opNorm η
    rw [norm_sub_rev] at h3
    linarith
  have h5 := mul_le_mul_of_nonneg_left h1 (norm_nonneg B)
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- The data `(χ, A, N)` of a seminorm of `𝓓'_Γ(W)`, for the cone `A` of `bigCone`. -/
private def bigConeIndex (B : F →L[ℝ] E) {χ : 𝓓(W, ℂ)} {V : Set E}
    (hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ V, t • ξ ∈ V) {ε : ℝ}
    (hχ : Disjoint (tsupport χ ×ˢ bigCone B V ε) Γ) (N : ℕ) : WaveFrontSeminormIndex W Γ where
  cutoff := χ
  cone := bigCone B V ε
  order := N
  isClosed_cone := isClosed_bigCone B V ε
  smul_mem_cone := smul_mem_bigCone B hVcone
  disjoint := hχ

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem disjoint_bigCone {B : F →L[ℝ] E} {χ : 𝓓(W, ℂ)} {V : Set E} {ε : ℝ}
    (hχ : ∀ p ∈ tsupport χ, ∀ η, infDist (B η) V ≤ ε * ‖η‖ → (p, η) ∉ Γ) :
    Disjoint (tsupport χ ×ˢ bigCone B V ε) Γ :=
  disjoint_left.2 fun ⟨p, η⟩ ⟨hp, hη⟩ ↦ hχ p hp η hη

omit [FiniteDimensional ℝ E] in
/-- The covectors `(y, η)` over the `1 / (n + 1)`-neighbourhood of `K` with `‖η‖ = 1` and `B η`
within `1 / (n + 1)` of `V` form a decreasing sequence of compact sets, whose intersection consists
of the unit covectors over `K` with `B η ∈ V`. -/
private theorem exists_cthickening_prod_subset (B : F →L[ℝ] E) {O : Set (F × F)} (hO : IsOpen O)
    {K : Set F} (hK : IsCompact K) {V : Set E} (hV : IsClosed V) (hV0 : (0 : E) ∈ V)
    (hKV : ∀ y ∈ K, ∀ η, ‖η‖ = 1 → B η ∈ V → (y, η) ∈ O) :
    ∃ n : ℕ, cthickening (1 / (n + 1 : ℝ)) K ×ˢ
      (sphere (0 : F) 1 ∩ {η | infDist (B η) V ≤ 1 / (n + 1 : ℝ)}) ⊆ O := by
  set S : ℕ → Set (F × F) := fun n ↦ cthickening (1 / (n + 1 : ℝ)) K ×ˢ
    (sphere (0 : F) 1 ∩ {η | infDist (B η) V ≤ 1 / (n + 1 : ℝ)})
  have hS (n : ℕ) : IsCompact (S n) := hK.cthickening.prod ((isCompact_sphere 0 1).inter_right
    (isClosed_le ((continuous_infDist_pt V).comp B.continuous) continuous_const))
  have hanti : Antitone S := fun m n hmn ↦ by
    have h : 1 / (n + 1 : ℝ) ≤ 1 / (m + 1 : ℝ) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hmn)
    exact prod_mono (cthickening_mono h K) (inter_subset_inter_right _ fun η hη ↦ hη.trans h)
  -- The intersection of the `S n` lies in `O`.
  have hsub : ⋂ n, S n ⊆ O := by
    rintro ⟨y, η⟩ hy
    simp only [mem_iInter, S, mem_prod, mem_inter_iff, mem_sphere_zero_iff_norm,
      mem_ofPred_eq] at hy
    have hyK : y ∈ K := by
      rw [← hK.isClosed.closure_eq, closure_eq_iInter_cthickening]
      simp only [mem_iInter]
      intro δ hδ
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
      exact cthickening_mono hn.le K (hy n).1
    have hηV : B η ∈ V := by
      rw [hV.mem_iff_infDist_zero ⟨0, hV0⟩]
      refine le_antisymm (le_of_forall_pos_le_add fun δ hδ ↦ ?_) infDist_nonneg
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
      linarith [(hy n).2.2]
    exact hKV y hyK η (hy 0).2.1 hηV
  exact exists_subset_nhds_of_isCompact' hanti.directed_ge hS (fun n ↦ (hS n).isClosed)
    (hO.mem_nhdsSet.2 hsub)

omit [FiniteDimensional ℝ E] in
/-- **No point of `Γ` near `K` in the directions close to `V`.** Let `Γ` be a cone of nonzero
covectors over `W`, closed in `W × (F \ {0})`, let `K ⊆ W` be compact and `V` a closed cone of `E`
containing `0`, and suppose that `B η ∉ V` for every covector `(y, η) ∈ Γ` over `K`. Then for some
`ε > 0`, no point of `Γ` lies over the `ε`-neighbourhood of `K` in a direction `η` with
`dist (B η, V) ≤ ε ‖η‖`. -/
theorem exists_forall_mem_thickening_forall_notMem (B : F →L[ℝ] E)
    (hΓ : IsOpen (((W : Set F) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    {K : Set F} (hK : IsCompact K) (hKW : K ⊆ W) {V : Set E} (hV : IsClosed V)
    (hV0 : (0 : E) ∈ V) (hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ V, t • ξ ∈ V)
    (hKV : ∀ y ∈ K, ∀ η, (y, η) ∈ Γ → B η ∉ V) :
    ∃ ε > 0, ∀ p ∈ thickening ε K, ∀ η, infDist (B η) V ≤ ε * ‖η‖ → (p, η) ∉ Γ := by
  -- Some `S n` lies in the open set `O` of nonzero covectors over `W` outside `Γ`.
  obtain ⟨n, hn⟩ := exists_cthickening_prod_subset B hΓ hK hV hV0 fun y hy η hη hηV ↦
    ⟨⟨hKW hy, fun (h0 : η = 0) ↦ by
      rw [h0, norm_zero] at hη
      exact zero_ne_one hη⟩, fun hΓη ↦ hKV y hy η hΓη hηV⟩
  set ε := 1 / (n + 1 : ℝ)
  refine ⟨ε, by positivity, fun p hp η hη hpη ↦ ?_⟩
  rcases eq_or_ne η 0 with rfl | hη0
  · exact hΓ0 _ hpη rfl
  -- The unit covector `‖η‖⁻¹ η` lies in `S n`, hence outside `Γ`, and `Γ` is a cone.
  have hpos : 0 < ‖η‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hη0)
  have hS : (p, ‖η‖⁻¹ • η) ∈ cthickening ε K ×ˢ
      (sphere (0 : F) 1 ∩ {η | infDist (B η) V ≤ ε}) := by
    refine ⟨thickening_subset_cthickening _ _ hp, ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀
        (norm_ne_zero_iff.2 hη0)]
    · change infDist (B (‖η‖⁻¹ • η)) V ≤ ε
      rw [map_smul, infDist_smul_of_smul_mem hVcone hpos]
      calc ‖η‖⁻¹ * infDist (B η) V ≤ ‖η‖⁻¹ * (ε * ‖η‖) := by gcongr
        _ = ε := by field_simp
  exact (hn hS).2 (hcone _ hpη _ hpos)

omit [FiniteDimensional ℝ E] in
/-- **A cutoff adapted to `Γ`.** Let `Γ` be a cone of nonzero covectors over `W`, closed in
`W × (F \ {0})`, let `K ⊆ W` be compact and `V` a closed cone of `E` containing `0`, and suppose
that `B η ∉ V` for every covector `(y, η) ∈ Γ` over `K`. Then for some `ε > 0` there is a cutoff `χ`
on `W`, equal to one on `K`, such that no point of `Γ` lies over the support of `χ` in a direction
`η` with `dist (B η, V) ≤ ε ‖η‖`: the hypothesis of
`TauCeti.WaveFrontSpace.exists_continuous_seminorm_one_add_norm_pow_mul_norm_tsum_le`. -/
theorem exists_cutoff_eqOn_one_forall_notMem (B : F →L[ℝ] E)
    (hΓ : IsOpen (((W : Set F) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    {K : Set F} (hK : IsCompact K) (hKW : K ⊆ W) {V : Set E} (hV : IsClosed V)
    (hV0 : (0 : E) ∈ V) (hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ V, t • ξ ∈ V)
    (hKV : ∀ y ∈ K, ∀ η, (y, η) ∈ Γ → B η ∉ V) :
    ∃ ε > 0, ∃ χ : 𝓓(W, ℂ), EqOn χ 1 K ∧
      ∀ p ∈ tsupport χ, ∀ η, infDist (B η) V ≤ ε * ‖η‖ → (p, η) ∉ Γ := by
  obtain ⟨ε, hε, hεΓ⟩ := exists_forall_mem_thickening_forall_notMem B hΓ hcone hΓ0 hK hKW hV hV0
    hVcone hKV
  obtain ⟨χ, hχ1, hχ⟩ := exists_complex_cutoff_tsupport_subset (Ω := W) (n := ⊤) hK
    (isOpen_thickening.inter W.isOpen) (fun y hy ↦ ⟨self_subset_thickening hε K hy, hKW hy⟩)
    inter_subset_right
  exact ⟨ε, hε, χ, fun y hy ↦ hχ1.self_of_nhdsSet y hy, fun p hp ↦ hεΓ p (hχ hp).1⟩

/-! ### Splitting the lattice series -/

/-- The cutoff `χ` as a smooth function supported in its own support. -/
private def cutoffK (χ : 𝓓(W, ℂ)) :
    𝓓_{⟨tsupport χ, χ.hasCompactSupport.isCompact⟩}(F, ℂ) :=
  ContDiffMapSupportedIn.of_support_subset χ.contDiff (subset_tsupport _)

section Measurable

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- The coefficients `(covolume L)⁻¹ f (ξ + B m)` of the lattice series, for the `m` with
`-m ∉ A`. -/
private def badCoeff (B : F →L[ℝ] E) (L : Submodule ℤ F) (A : Set F) (f : E → ℂ) (ξ : E)
    (m : ZLattice.dual L) : ℂ :=
  {m : ZLattice.dual L | -(m : F) ∉ A}.indicator
    (fun m ↦ (ZLattice.covolume L : ℂ)⁻¹ * f (ξ + B m)) m

/-- The terms `(covolume L)⁻¹ f (ξ + B m) G (-m)` of the lattice series, for the `m` with
`-m ∈ A`. -/
private def goodTerm (B : F →L[ℝ] E) (L : Submodule ℤ F) (A : Set F) (f : E → ℂ) (G : F → ℂ)
    (ξ : E) (m : ZLattice.dual L) : ℂ :=
  {m : ZLattice.dual L | -(m : F) ∈ A}.indicator
    (fun m ↦ (ZLattice.covolume L : ℂ)⁻¹ * (f (ξ + B m) * G (-m))) m

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] in
/-- Peetre's inequality for the frequencies of the lattice series:
`1 + ‖ξ‖ ≤ (1 + ‖ξ + B m‖) ((1 + ‖B‖) (1 + ‖m‖))`. -/
private theorem one_add_norm_le_mul (B : F →L[ℝ] E) (ξ : E) (m : F) :
    1 + ‖ξ‖ ≤ (1 + ‖ξ + B m‖) * ((1 + ‖B‖) * (1 + ‖m‖)) := by
  have h1 : ‖ξ‖ ≤ ‖ξ + B m‖ + ‖B m‖ := by
    simpa using norm_sub_le (ξ + B m) (B m)
  have h2 := B.le_opNorm m
  have h3 := mul_nonneg (norm_nonneg (ξ + B m)) (norm_nonneg B)
  have h4 := mul_nonneg (norm_nonneg (ξ + B m)) (mul_nonneg (norm_nonneg B) (norm_nonneg m))
  have h5 := mul_nonneg (norm_nonneg (ξ + B m)) (norm_nonneg m)
  nlinarith [norm_nonneg B, norm_nonneg m]

/-- A decay bound is nonnegative. -/
private theorem nonneg_of_one_add_norm_pow_mul_norm_le {X G : Type*} [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup G] {f : X → G} {x : X} {n : ℕ} {C : ℝ}
    (hC : (1 + ‖x‖) ^ n * ‖f x‖ ≤ C) : 0 ≤ C :=
  (by positivity : (0 : ℝ) ≤ (1 + ‖x‖) ^ n * ‖f x‖).trans hC

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **A term in `A`.** If `f` decays to order `N` with constant `C` and `G` decays on `A` to order
`N + q` with constant `S`, then the term of index `m` of the lattice series is at most
`‖(covolume L)⁻¹‖ (1 + ‖B‖)ᴺ C S (1 + ‖ξ‖)⁻ᴺ (1 + ‖m‖)⁻ᵠ` when `-m ∈ A`, and vanishes
otherwise. -/
private theorem norm_goodTerm_le (B : F →L[ℝ] E) (L : Submodule ℤ F) {A : Set F} {f : E → ℂ}
    {G : F → ℂ} {N q : ℕ} {C S : ℝ} (hS0 : 0 ≤ S) (hC : ∀ η, (1 + ‖η‖) ^ N * ‖f η‖ ≤ C)
    (hS : ∀ ζ ∈ A, (1 + ‖ζ‖) ^ (N + q) * ‖G ζ‖ ≤ S) (ξ : E) (m : ZLattice.dual L) :
    ‖goodTerm B L A f G ξ m‖ ≤ ‖(ZLattice.covolume L : ℂ)⁻¹‖ * (1 + ‖B‖) ^ N * C * S *
      ((1 + ‖ξ‖) ^ N)⁻¹ * ((1 + ‖(m : F)‖) ^ q)⁻¹ := by
  set a : ℂ := (ZLattice.covolume L : ℂ)⁻¹
  have hC0 := nonneg_of_one_add_norm_pow_mul_norm_le (hC 0)
  rw [mul_right_comm _ ((1 + ‖ξ‖) ^ N)⁻¹, ← div_eq_mul_inv _ ((1 + ‖ξ‖) ^ N),
    le_div_iff₀' (by positivity)]
  by_cases hm : -(m : F) ∈ A
  · rw [goodTerm, indicator_of_mem (s := {m : ZLattice.dual L | -(m : F) ∈ A}) hm, norm_mul,
      norm_mul]
    have h2 := hS _ hm
    rw [norm_neg] at h2
    have h2' : (1 + ‖(m : F)‖) ^ N * ‖G (-m)‖ ≤ S * ((1 + ‖(m : F)‖) ^ q)⁻¹ := by
      rw [le_mul_inv_iff₀ (by positivity)]
      calc _ = (1 + ‖(m : F)‖) ^ (N + q) * ‖G (-m)‖ := by ring
        _ ≤ S := h2
    have hP := pow_le_pow_left₀ (by positivity) (one_add_norm_le_mul B ξ (m : F)) N
    rw [mul_pow, mul_pow] at hP
    calc (1 + ‖ξ‖) ^ N * (‖a‖ * (‖f (ξ + B m)‖ * ‖G (-m)‖))
        ≤ ((1 + ‖ξ + B m‖) ^ N * ((1 + ‖B‖) ^ N * (1 + ‖(m : F)‖) ^ N)) *
            (‖a‖ * (‖f (ξ + B m)‖ * ‖G (-m)‖)) := by gcongr
      _ = ‖a‖ * (1 + ‖B‖) ^ N * (((1 + ‖ξ + B m‖) ^ N * ‖f (ξ + B m)‖) *
          ((1 + ‖(m : F)‖) ^ N * ‖G (-m)‖)) := by ring
      _ ≤ ‖a‖ * (1 + ‖B‖) ^ N * (C * (S * ((1 + ‖(m : F)‖) ^ q)⁻¹)) := by
          gcongr
          · exact hC _
      _ = _ := by ring
  · rw [goodTerm, indicator_of_notMem (s := {m : ZLattice.dual L | -(m : F) ∈ A}) hm, norm_zero,
      mul_zero]
    positivity

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A coefficient off `A` depends continuously on a parameter on which `f (ξ + B m)` depends
continuously. -/
private theorem continuous_badCoeff (B : F →L[ℝ] E) (L : Submodule ℤ F) {X : Type*}
    [TopologicalSpace X] {A : Set F} {f : X → E → ℂ} {ξ : X → E} {m : ZLattice.dual L}
    (hf : Continuous fun x ↦ f x (ξ x + B m)) :
    Continuous fun x ↦ badCoeff B L A (f x) (ξ x) m := by
  by_cases hm : -(m : F) ∈ A
  · simp only [badCoeff, mem_ofPred_eq, hm, not_true_eq_false, not_false_eq_true,
      indicator_of_notMem]
    exact continuous_const
  · simp only [badCoeff, indicator_of_mem (s := {m : ZLattice.dual L | -(m : F) ∉ A}) hm]
    exact continuous_const.mul hf

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The terms in `A`.** If `f` decays to order `N` with constant `C` and `G` decays on `A` to
order `N + q` with constant `S`, then the sum of the terms of the lattice series with `-m ∈ A`
decays to order `N` in `ξ`. -/
private theorem one_add_norm_pow_mul_norm_tsum_goodTerm_le (B : F →L[ℝ] E) (L : Submodule ℤ F)
    {A : Set F} {f : E → ℂ} {G : F → ℂ} {N q : ℕ} {C S : ℝ} (hS0 : 0 ≤ S)
    (hC : ∀ η, (1 + ‖η‖) ^ N * ‖f η‖ ≤ C) (hS : ∀ ζ ∈ A, (1 + ‖ζ‖) ^ (N + q) * ‖G ζ‖ ≤ S)
    (hq : Summable fun m : ZLattice.dual L ↦ ((1 + ‖(m : F)‖) ^ q)⁻¹) (ξ : E) :
    (1 + ‖ξ‖) ^ N * ‖∑' m, goodTerm B L A f G ξ m‖ ≤
      ‖(ZLattice.covolume L : ℂ)⁻¹‖ * (1 + ‖B‖) ^ N * C * S *
        ∑' m : ZLattice.dual L, ((1 + ‖(m : F)‖) ^ q)⁻¹ := by
  have hle := tsum_of_norm_bounded (hq.hasSum.mul_left _) (norm_goodTerm_le B L hS0 hC hS ξ)
  calc (1 + ‖ξ‖) ^ N * ‖∑' m, goodTerm B L A f G ξ m‖
      ≤ (1 + ‖ξ‖) ^ N * (‖(ZLattice.covolume L : ℂ)⁻¹‖ * (1 + ‖B‖) ^ N * C * S *
          ((1 + ‖ξ‖) ^ N)⁻¹ * ∑' m : ZLattice.dual L, ((1 + ‖(m : F)‖) ^ q)⁻¹) := by gcongr
    _ = _ := by field_simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The splitting of the lattice series.** The lattice series is the sum of its terms with
`-m ∈ A`, and of the pairing of `T` with the series of the remaining terms, a smooth function
supported in `tsupport χ`. -/
private theorem tsum_eq_add (B : F →L[ℝ] E) (T : 𝓓'(W, ℂ)) {V : Set E} (hV0 : (0 : E) ∈ V)
    {ε : ℝ} (χ : 𝓓(W, ℂ)) (L : Submodule ℤ F) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hdecay : ∀ N : ℕ, ∃ C, ∀ ζ ∈ bigCone B V ε, (1 + ‖ζ‖) ^ N * ‖T.localFourier χ ζ‖ ≤ C)
    {f : E → ℂ} (hf : ∃ C, ∀ η, (1 + ‖η‖) ^ 0 * ‖f η‖ ≤ C) (ξ : E)
    (hbad : Summable fun m ↦ badCoeff B L (bigCone B V ε) f ξ m • (cutoffK χ).modulate (m : F)) :
    ∑' m : ZLattice.dual L, (ZLattice.covolume L : ℂ)⁻¹ *
        (f (ξ + B m) * T.localFourier χ (-m)) =
      (∑' m, goodTerm B L (bigCone B V ε) f (T.localFourier χ) ξ m) +
      T.complexPairing (ofSupportedIn χ.tsupport_subset (∑' m, badCoeff B L (bigCone B V ε)
        f ξ m • (cutoffK χ).modulate (m : F))) := by
  set A := bigCone B V ε
  -- The terms with `-m ∉ A` sum to the pairing of `T` with the series of modulated cutoffs.
  have hb : HasSum (fun m : ZLattice.dual L ↦ badCoeff B L A f ξ m * T.localFourier χ (-m))
      (T.complexPairing (ofSupportedIn χ.tsupport_subset
        (∑' m, badCoeff B L A f ξ m • (cutoffK χ).modulate (m : F)))) := by
    have hfun : (fun m : ZLattice.dual L ↦ badCoeff B L A f ξ m * T.localFourier χ (-m)) =
        (T.complexPairing.comp (ofSupportedInCLM ℂ χ.tsupport_subset)) ∘
          fun m ↦ badCoeff B L A f ξ m • (cutoffK χ).modulate (m : F) := by
      ext m
      rw [Function.comp_apply, map_smul, smul_eq_mul, ContinuousLinearMap.comp_apply,
        coe_ofSupportedInCLM, localFourier_eq_complexPairing_modulate T χ.tsupport_subset
          (f := cutoffK χ) (ContDiffMapSupportedIn.coe_of_support_subset _ _), neg_neg]
    rw [hfun]
    exact (T.complexPairing.comp (ofSupportedInCLM ℂ χ.tsupport_subset)).hasSum hbad.hasSum
  -- The terms with `-m ∈ A` are summable, by the decay of `T` on `A`.
  set q := Module.finrank ℤ (ZLattice.dual L) + 1
  have hq := ZLattice.summable_one_add_norm_pow_inv (ZLattice.dual L) (r := q) (by omega)
  obtain ⟨C₀, hC₀⟩ := hf
  obtain ⟨C, hC⟩ := hdecay q
  have hC0 := nonneg_of_one_add_norm_pow_mul_norm_le
    (hC 0 (by simp [A, bigCone, infDist_zero_of_mem hV0]))
  have hg : Summable (goodTerm B L A f (T.localFourier χ) ξ) :=
    Summable.of_norm_bounded (hq.mul_left _) (norm_goodTerm_le B L (N := 0) hC0 hC₀
      (fun ζ hζ ↦ by simpa using hC ζ hζ) ξ)
  refine ((hg.hasSum.add hb).congr_fun fun m ↦ ?_).tsum_eq
  by_cases hm : -(m : F) ∈ A
  · simp [goodTerm, badCoeff, hm]
  · simp [goodTerm, badCoeff, hm, mul_assoc]

/-! ### Estimates for the two parts -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The coefficients off `A`.** For `ξ ∈ V` and `-m ∉ A`, `‖ξ + B m‖` is comparable to
`1 + ‖ξ‖ + ‖m‖`, so a decay estimate of order `M` for `f` gives one for the coefficients. -/
private theorem pow_mul_one_add_pow_mul_norm_badCoeff_le (B : F →L[ℝ] E) (L : Submodule ℤ F)
    {V : Set E} {ε : ℝ} (hε : 0 < ε) {f : E → ℂ} {M : ℕ} {C : ℝ}
    (hC : ∀ η, (1 + ‖η‖) ^ M * ‖f η‖ ≤ C) {ξ : E} (hξ : ξ ∈ V) (m : ZLattice.dual L) :
    (ε / (1 + ‖B‖ + ε)) ^ M * (1 + ‖ξ‖ + ‖(m : F)‖) ^ M * ‖badCoeff B L (bigCone B V ε) f ξ m‖ ≤
      ‖(ZLattice.covolume L : ℂ)⁻¹‖ * C := by
  have hC0 := nonneg_of_one_add_norm_pow_mul_norm_le (hC 0)
  by_cases hm : -(m : F) ∈ bigCone B V ε
  · simp only [badCoeff, mem_ofPred_eq, hm, not_true_eq_false, not_false_eq_true,
      indicator_of_notMem, norm_zero, mul_zero]
    positivity
  · rw [badCoeff, indicator_of_mem (s := {m : ZLattice.dual L | -(m : F) ∉ bigCone B V ε}) hm,
      norm_mul]
    have hsep := mul_add_le_norm_sub B hε hξ hm
    rw [show B (-(m : F)) - ξ = -(ξ + B m) by rw [map_neg]; abel, norm_neg, norm_neg] at hsep
    set c := ε / (1 + ‖B‖ + ε)
    have hc1 : c ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [norm_nonneg B]
    have key : c * (1 + ‖ξ‖ + ‖(m : F)‖) ≤ 1 + ‖ξ + B m‖ := by nlinarith
    calc c ^ M * (1 + ‖ξ‖ + ‖(m : F)‖) ^ M *
          (‖(ZLattice.covolume L : ℂ)⁻¹‖ * ‖f (ξ + B m)‖)
        = ‖(ZLattice.covolume L : ℂ)⁻¹‖ * ((c * (1 + ‖ξ‖ + ‖(m : F)‖)) ^ M *
            ‖f (ξ + B m)‖) := by rw [mul_pow]; ring
      _ ≤ ‖(ZLattice.covolume L : ℂ)⁻¹‖ * ((1 + ‖ξ + B m‖) ^ M * ‖f (ξ + B m)‖) := by gcongr
      _ ≤ ‖(ZLattice.covolume L : ℂ)⁻¹‖ * C := by gcongr; exact hC _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The decay estimate of `pow_mul_one_add_pow_mul_norm_badCoeff_le`, with the constant
`(ε / (1 + ‖B‖ + ε)) ^ M` moved to the right-hand side. -/
private theorem one_add_add_pow_mul_norm_badCoeff_le (B : F →L[ℝ] E) (L : Submodule ℤ F)
    {V : Set E} {ε : ℝ} (hε : 0 < ε) {f : E → ℂ} {M : ℕ} {C : ℝ}
    (hC : ∀ η, (1 + ‖η‖) ^ M * ‖f η‖ ≤ C) {ξ : E} (hξ : ξ ∈ V) (m : ZLattice.dual L) :
    (1 + ‖ξ‖ + ‖(m : F)‖) ^ M * ‖badCoeff B L (bigCone B V ε) f ξ m‖ ≤
      ‖(ZLattice.covolume L : ℂ)⁻¹‖ * C / (ε / (1 + ‖B‖ + ε)) ^ M := by
  rw [le_div_iff₀ (by positivity)]
  linarith [pow_mul_one_add_pow_mul_norm_badCoeff_le B L hε hC hξ m]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Domination of the Fourier series off `A`.** For a family `S` of functions decaying rapidly,
uniformly, the products of the coefficients off `A`, weighted by `(1 + ‖ξ‖) ^ N`, with the
seminorms of the modulated cutoffs are dominated by nonnegative summable sequences, uniformly in
`f ∈ S` and `ξ ∈ V`. -/
private theorem exists_summable_one_add_pow_mul_norm_badCoeff_mul_seminorm_le (B : F →L[ℝ] E)
    (L : Submodule ℤ F) [DiscreteTopology L] [IsZLattice ℝ L] {V : Set E} {ε : ℝ} (hε : 0 < ε)
    (χ : 𝓓(W, ℂ)) (N : ℕ) {S : Set (E → ℂ)}
    (hS : ∀ M : ℕ, ∃ C, ∀ f ∈ S, ∀ η, (1 + ‖η‖) ^ M * ‖f η‖ ≤ C) :
    ∃ b : ℕ → ZLattice.dual L → ℝ, (∀ k, Summable (b k)) ∧ (∀ k m, 0 ≤ b k m) ∧
      ∀ f ∈ S, ∀ ξ ∈ V, ∀ k m, (1 + ‖ξ‖) ^ N * ‖badCoeff B L (bigCone B V ε) f ξ m‖ *
        N[ℂ]_{⟨tsupport χ, χ.hasCompactSupport.isCompact⟩, k}
          ((cutoffK χ).modulate (m : F)) ≤ b k m := by
  have ha (M : ℕ) : ∃ C, ∀ (p : {p : (E → ℂ) × E // p.1 ∈ S ∧ p.2 ∈ V}) (m : ZLattice.dual L),
      (1 + ‖p.val.2‖ + ‖(m : F)‖) ^ M * ‖badCoeff B L (bigCone B V ε) p.val.1 p.val.2 m‖ ≤ C := by
    obtain ⟨C, hC⟩ := hS M
    exact ⟨_, fun p m ↦
      one_add_add_pow_mul_norm_badCoeff_le B L hε (hC p.val.1 p.property.1) p.property.2 m⟩
  obtain ⟨b, hb, hb0, hbound⟩ :=
    ContDiffMapSupportedIn.exists_summable_one_add_pow_mul_norm_mul_seminorm_modulate_le
      (ZLattice.dual L) (w := fun p : {p : (E → ℂ) × E // p.1 ∈ S ∧ p.2 ∈ V} ↦ ‖p.val.2‖)
      (fun _ ↦ norm_nonneg _) ha (cutoffK χ) N
  exact ⟨b, hb, hb0, fun f hf ξ hξ ↦ hbound ⟨(f, ξ), hf, hξ⟩⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The Fourier series off `A` converges in `𝓓_K`, for a rapidly decreasing `f`. -/
private theorem summable_badCoeff_smul_modulate (B : F →L[ℝ] E) (L : Submodule ℤ F)
    [DiscreteTopology L] [IsZLattice ℝ L] {V : Set E} {ε : ℝ} (hε : 0 < ε) (χ : 𝓓(W, ℂ))
    {f : E → ℂ} (hf : ∀ M : ℕ, ∃ C, ∀ η, (1 + ‖η‖) ^ M * ‖f η‖ ≤ C) {ξ : E} (hξ : ξ ∈ V) :
    Summable fun m ↦ badCoeff B L (bigCone B V ε) f ξ m • (cutoffK χ).modulate (m : F) := by
  obtain ⟨b, hb, -, hbound⟩ := exists_summable_one_add_pow_mul_norm_badCoeff_mul_seminorm_le
    (V := V) B L hε χ 0 (S := {f}) fun M ↦ (hf M).imp fun C hC g hg ↦ by
      rw [mem_singleton_iff.1 hg]
      exact hC
  refine ContDiffMapSupportedIn.summable_smul_of_le hb fun k m ↦ ?_
  simpa using hbound f rfl ξ hξ k m

/-! ### Compact sets of test functions -/

/-- **The weighted Fourier series off `A` form a compact set.** For `ξ ∈ V`, the series of the
modulated cutoffs with the coefficients off `A` weighted by `(1 + ‖ξ‖) ^ N` depends continuously on
`ξ` and tends to zero at infinity, so these series and `0` form a compact set. -/
private theorem isCompact_insert_range_tsum (B : F →L[ℝ] E) (L : Submodule ℤ F)
    [DiscreteTopology L] [IsZLattice ℝ L] {V : Set E} (hV : IsClosed V) {ε : ℝ} (hε : 0 < ε)
    (χ : 𝓓(W, ℂ)) (φ : 𝓓(U, ℂ)) (N : ℕ) :
    IsCompact (insert 0 (range fun ξ : V ↦ ∑' m : ZLattice.dual L,
      ((((1 + ‖(ξ : E)‖) ^ N : ℝ) : ℂ) * badCoeff B L (bigCone B V ε) (𝓕 (φ : E → ℂ)) ξ m) •
        (cutoffK χ).modulate (m : F))) :=
  ContDiffMapSupportedIn.isCompact_insert_range_tsum_one_add_pow_mul_smul_modulate
    (ZLattice.dual L) (w := fun ξ : V ↦ ‖(ξ : E)‖)
    (a := fun ξ m ↦ badCoeff B L (bigCone B V ε) (𝓕 (φ : E → ℂ)) ξ m) (fun _ ↦ norm_nonneg _)
    (continuous_norm.comp continuous_subtypeVal)
    (tendsto_norm_cocompact_atTop.comp hV.isClosedEmbedding_subtypeVal.tendsto_cocompact)
    (fun _ ↦ continuous_badCoeff B L ((φ.continuous.integrable_of_hasCompactSupport
      φ.hasCompactSupport).continuous_fourier.comp (continuous_subtypeVal.add continuous_const)))
    (fun M ↦ by
      obtain ⟨C, hC⟩ := exists_one_add_norm_pow_mul_norm_fourier_le φ.contDiff φ.hasCompactSupport M
      exact ⟨_, fun ξ m ↦ one_add_add_pow_mul_norm_badCoeff_le B L hε hC ξ.property m⟩)
    (cutoffK χ) N

/-- **The Fourier series off `A` for a compact set of cutoffs.** At `ξ = 0`, the series of the
modulated cutoffs with the coefficients off `A` depends continuously on the cutoff `ψ`, so over a
compact set of cutoffs these series form a compact set. -/
private theorem isCompact_range_tsum (B : F →L[ℝ] E) (L : Submodule ℤ F) [DiscreteTopology L]
    [IsZLattice ℝ L] {ε : ℝ} (hε : 0 < ε) (χ : 𝓓(W, ℂ)) {Q : Set 𝓓(U, ℂ)} (hQ : IsCompact Q) :
    IsCompact (range fun ψ : Q ↦ ∑' m : ZLattice.dual L,
      badCoeff B L (bigCone B {0} ε) (𝓕 ((ψ : 𝓓(U, ℂ)) : E → ℂ)) 0 m •
        (cutoffK χ).modulate (m : F)) := by
  have : CompactSpace Q := isCompact_iff_compactSpace.1 hQ
  obtain ⟨b, hb, -, hbound'⟩ := exists_summable_one_add_pow_mul_norm_badCoeff_mul_seminorm_le
    (V := {0}) B L hε χ 0 (S := (fun ψ : 𝓓(U, ℂ) ↦ 𝓕 (ψ : E → ℂ)) '' Q) fun M ↦
      (exists_forall_one_add_norm_pow_mul_norm_fourier_le hQ M).imp fun C hC ↦ by
        rintro _ ⟨ψ, hψ, rfl⟩
        exact hC ψ hψ
  have hbound (ψ : Q) (k : ℕ) (m : ZLattice.dual L) :
      ‖badCoeff B L (bigCone B {0} ε) (𝓕 ((ψ : 𝓓(U, ℂ)) : E → ℂ)) 0 m‖ *
        N[ℂ]_{⟨tsupport χ, χ.hasCompactSupport.isCompact⟩, k}
          ((cutoffK χ).modulate (m : F)) ≤ b k m := by
    simpa using hbound' _ ⟨ψ, ψ.property, rfl⟩ 0 (mem_singleton 0) k m
  -- Each coefficient is continuous in `ψ`.
  have hcont (m : ZLattice.dual L) : Continuous fun ψ : Q ↦
      badCoeff B L (bigCone B {0} ε) (𝓕 ((ψ : 𝓓(U, ℂ)) : E → ℂ)) 0 m :=
    continuous_badCoeff B L ((continuous_fourier_apply (Ω := U) _).comp continuous_subtypeVal)
  exact isCompact_range (ContDiffMapSupportedIn.continuous_tsum_smul_of_dominated hb hbound hcont)

/-- Combining the bounds on the terms in `A` and off `A`. -/
private theorem mul_norm_add_le_seminorm {X : Type*} [AddCommGroup X] [Module ℂ X]
    (p₁ p₂ : Seminorm ℂ X) (u : X) {w K₀ : ℝ} (hw : 0 ≤ w) (hK₀ : 0 ≤ K₀) {g c : ℂ}
    (hg : w * ‖g‖ ≤ K₀ * p₁ u) (hc : w * ‖c‖ ≤ p₂ u) :
    w * ‖g + c‖ ≤ (K₀.toNNReal • p₁ + p₂) u :=
  calc w * ‖g + c‖ ≤ w * ‖g‖ + w * ‖c‖ := by rw [← mul_add]; gcongr; exact norm_add_le _ _
    _ ≤ K₀ * p₁ u + p₂ u := add_le_add hg hc
    _ = (K₀.toNNReal • p₁ + p₂) u := by simp [NNReal.smul_def, Real.coe_toNNReal _ hK₀]

/-- **The estimate behind both seminorm bounds.** Let `φ x`, `x ∈ X`, be cutoffs whose Fourier
transforms decay to order `N` with a common constant, and let `ξ x` lie in a cone `V` containing
`0`. If the weighted series of the terms off `A` form a compact set together with `0`, then the
weighted lattice series is bounded by a continuous seminorm `p` of `𝓓'_Γ(W)`. -/
private theorem exists_seminorm_tsum_le_of_isCompact (B : F →L[ℝ] E) {χ : 𝓓(W, ℂ)} {V : Set E}
    (hV0 : (0 : E) ∈ V) (hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ V, t • ξ ∈ V) {ε : ℝ} (hε : 0 < ε)
    (hχΓ : Disjoint (tsupport χ ×ˢ bigCone B V ε) Γ) (L : Submodule ℤ F) [DiscreteTopology L]
    [IsZLattice ℝ L] {X : Type*} {φ : X → 𝓓(U, ℂ)} {ξ : X → E} (hξV : ∀ x, ξ x ∈ V) {N : ℕ}
    {C : ℝ} (hC : ∀ x η, (1 + ‖η‖) ^ N * ‖𝓕 (φ x : E → ℂ) η‖ ≤ C)
    (hS : IsCompact (insert 0 (range fun x : X ↦ ∑' m : ZLattice.dual L,
      ((((1 + ‖ξ x‖) ^ N : ℝ) : ℂ) * badCoeff B L (bigCone B V ε) (𝓕 (φ x : E → ℂ)) (ξ x) m) •
        (cutoffK χ).modulate (m : F)))) :
    ∃ p : Seminorm ℂ (WaveFrontSpace W Γ), Continuous p ∧ ∀ u : WaveFrontSpace W Γ, ∀ x : X,
      (1 + ‖ξ x‖) ^ N * ‖∑' m : ZLattice.dual L, (ZLattice.covolume L : ℂ)⁻¹ *
        (𝓕 (φ x : E → ℂ) (ξ x + B m) * u.toDistribution.localFourier χ (-m))‖ ≤ p u := by
  set q := Module.finrank ℤ (ZLattice.dual L) + 1
  have hq := ZLattice.summable_one_add_norm_pow_inv (ZLattice.dual L) (r := q) (by omega)
  obtain ⟨p', hp', hp'le⟩ := exists_continuous_seminorm_norm_complexPairing_le (Γ := Γ)
    (hS.image (continuous_ofSupportedIn χ.tsupport_subset))
  set i := bigConeIndex B hVcone hχΓ (N + q)
  set K₀ : ℝ := ‖(ZLattice.covolume L : ℂ)⁻¹‖ * (1 + ‖B‖) ^ N * max C 0 *
    ∑' m : ZLattice.dual L, ((1 + ‖(m : F)‖) ^ q)⁻¹
  have hK₀ : 0 ≤ K₀ := by positivity
  refine ⟨K₀.toNNReal • WaveFrontSpace.seminorm i + p',
    ((continuous_seminorm i).const_smul _).add hp', fun u x ↦ ?_⟩
  set T := u.toDistribution
  -- The decay of `T` on the cone `A`, from the seminorms `‖T‖_{χ,A,M}`.
  have hdecay (M : ℕ) : ∃ C, ∀ ζ ∈ bigCone B V ε, (1 + ‖ζ‖) ^ M * ‖T.localFourier χ ζ‖ ≤ C :=
    ⟨_, fun ζ hζ ↦ le_seminorm (bigConeIndex B hVcone hχΓ M) u hζ⟩
  -- The series off `A` converges.
  have hbad := summable_badCoeff_smul_modulate B L hε χ
    (exists_one_add_norm_pow_mul_norm_fourier_le (φ x).contDiff (φ x).hasCompactSupport) (hξV x)
  rw [tsum_eq_add B T hV0 χ L hdecay
    (exists_one_add_norm_pow_mul_norm_fourier_le (φ x).contDiff (φ x).hasCompactSupport 0) (ξ x)
    hbad]
  -- The terms in `A`.
  have hgood := one_add_norm_pow_mul_norm_tsum_goodTerm_le B L (apply_nonneg _ u)
    (fun η ↦ (hC x η).trans (le_max_left C 0)) (fun ζ hζ ↦ le_seminorm i u hζ) hq (ξ x)
  -- The terms off `A`: the weighted series lies in the compact set `hS`.
  have hbadle := hp'le u (ofSupportedIn χ.tsupport_subset (∑' m : ZLattice.dual L,
      ((((1 + ‖ξ x‖) ^ N : ℝ) : ℂ) * badCoeff B L (bigCone B V ε) (𝓕 (φ x : E → ℂ)) (ξ x) m) •
        (cutoffK χ).modulate (m : F)))
    (mem_image_of_mem _ (mem_insert_of_mem _ ⟨x, rfl⟩))
  rw [← mul_norm_complexPairing_tsum_smul T χ.tsupport_subset (by positivity) hbad] at hbadle
  exact mul_norm_add_le_seminorm _ _ u (by positivity) hK₀
    (hgood.trans_eq (by simp only [K₀]; ring)) hbadle

/-! ### The seminorm estimates -/

/-- **The weighted lattice series is bounded by a continuous seminorm.** Let `B : F →L[ℝ] E`,
let `V` be a closed cone of `E`, and let `χ` be a cutoff on `W` such that no point of `Γ` lies over
the support of `χ` in a direction `η` with `dist (B η, V) ≤ ε ‖η‖`, for some `ε > 0`. Then for
every cutoff `φ` on an open set of `E` and every `N`, the lattice series

`(1 + ‖ξ‖) ^ N ∑ m : L^∨, (covolume L)⁻¹ 𝓕 φ (ξ + B m) T (χ e_(-m))`, `ξ ∈ V`,

is bounded by a continuous seminorm of `𝓓'_Γ(W)`, uniformly in `ξ ∈ V`. -/
theorem exists_continuous_seminorm_one_add_norm_pow_mul_norm_tsum_le (B : F →L[ℝ] E)
    {χ : 𝓓(W, ℂ)} {V : Set E} (hV : IsClosed V) (hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ V, t • ξ ∈ V)
    {ε : ℝ} (hε : 0 < ε) (hχ : ∀ p ∈ tsupport χ, ∀ η, infDist (B η) V ≤ ε * ‖η‖ → (p, η) ∉ Γ)
    (L : Submodule ℤ F) [DiscreteTopology L] [IsZLattice ℝ L] (φ : 𝓓(U, ℂ)) (N : ℕ) :
    ∃ p : Seminorm ℂ (WaveFrontSpace W Γ), Continuous p ∧ ∀ u : WaveFrontSpace W Γ, ∀ ξ ∈ V,
      (1 + ‖ξ‖) ^ N * ‖∑' m : ZLattice.dual L, (ZLattice.covolume L : ℂ)⁻¹ *
        (𝓕 (φ : E → ℂ) (ξ + B m) * u.toDistribution.localFourier χ (-m))‖ ≤ p u := by
  rcases V.eq_empty_or_nonempty with rfl | ⟨ξ₀, hξ₀⟩
  · exact ⟨0, continuous_const, fun u ξ hξ ↦ absurd hξ (notMem_empty ξ)⟩
  have hV0 := hV.zero_mem_of_smul_mem hVcone hξ₀
  obtain ⟨C, hC⟩ :=
    exists_one_add_norm_pow_mul_norm_fourier_le φ.contDiff φ.hasCompactSupport N
  -- The family of cutoffs is constant, indexed by the points of the cone.
  obtain ⟨p, hp, hpV⟩ := exists_seminorm_tsum_le_of_isCompact B hV0 hVcone hε
    (disjoint_bigCone hχ) L (X := V) (φ := fun _ ↦ φ) (ξ := (↑)) Subtype.property
    (fun _ ↦ hC) (isCompact_insert_range_tsum B L hV hε χ φ N)
  exact ⟨p, hp, fun u ξ hξ ↦ hpV u ⟨ξ, hξ⟩⟩

/-- **The lattice series on a compact set of cutoffs is bounded by a continuous seminorm.** Let
`B : F →L[ℝ] E`, and let `χ` be a cutoff on `W` such that no point of `Γ` lies over the support of
`χ` in a direction `η` with `‖B η‖ ≤ ε ‖η‖`, for some `ε > 0`. Then for every compact set `Q` of
cutoffs on an open set of `E`, the lattice series

`∑ m : L^∨, (covolume L)⁻¹ 𝓕 ψ (B m) T (χ e_(-m))`, `ψ ∈ Q`,

is bounded by a continuous seminorm of `𝓓'_Γ(W)`, uniformly in `ψ ∈ Q`. -/
theorem exists_continuous_seminorm_norm_tsum_le (B : F →L[ℝ] E) {χ : 𝓓(W, ℂ)} {ε : ℝ}
    (hε : 0 < ε) (hχ : ∀ p ∈ tsupport χ, ∀ η, ‖B η‖ ≤ ε * ‖η‖ → (p, η) ∉ Γ)
    (L : Submodule ℤ F) [DiscreteTopology L] [IsZLattice ℝ L] {Q : Set 𝓓(U, ℂ)}
    (hQ : IsCompact Q) :
    ∃ p : Seminorm ℂ (WaveFrontSpace W Γ), Continuous p ∧ ∀ u : WaveFrontSpace W Γ, ∀ ψ ∈ Q,
      ‖∑' m : ZLattice.dual L, (ZLattice.covolume L : ℂ)⁻¹ *
        (𝓕 (ψ : E → ℂ) (B m) * u.toDistribution.localFourier χ (-m))‖ ≤ p u := by
  obtain ⟨C, hC⟩ := exists_forall_one_add_norm_pow_mul_norm_fourier_le hQ 0
  -- The family of cutoffs is `Q`, all at the point `ξ = 0`, with weight order `0`.
  obtain ⟨p, hp, hpQ⟩ := exists_seminorm_tsum_le_of_isCompact B (mem_singleton 0)
    forall_smul_mem_singleton_zero hε
    (disjoint_bigCone fun p hp η hη ↦ hχ p hp η (by simpa using hη)) L (X := Q)
    (φ := fun ψ : Q ↦ (ψ : 𝓓(U, ℂ)))
    (ξ := fun _ ↦ 0) (fun _ ↦ mem_singleton 0) (N := 0) (fun ψ ↦ hC ψ ψ.property) (by
      simpa only [pow_zero, Complex.ofReal_one, one_mul] using
        (isCompact_range_tsum B L hε χ hQ).insert 0)
  refine ⟨p, hp, fun u ψ hψ ↦ ?_⟩
  simpa using hpQ u ⟨ψ, hψ⟩

end Measurable

end WaveFrontSpace

end TauCeti
